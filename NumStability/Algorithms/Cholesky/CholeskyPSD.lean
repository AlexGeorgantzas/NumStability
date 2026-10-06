-- Algorithms/Cholesky/CholeskyPSD.lean
--
-- §10.3: Positive semidefinite matrices.
--
-- Theorem 10.9: Existence of Cholesky for PSD (non-pivoted: A = R^T R).
-- Lemma 10.10: Schur complement perturbation identity.
-- Lemma 10.12: W-norm bound in terms of κ₂(A₁₁).
-- Lemma 10.13: Complete pivoting bound ‖W‖² ≤ (n−r)(4^r − 1)/3.
-- Theorem 10.14: Error analysis for PSD Cholesky with complete pivoting.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.Cholesky.CholeskySpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.3  Positive semidefinite predicate
-- ============================================================

/-- **Positive semidefinite matrix**: symmetric with x^T A x ≥ 0 for all x. -/
def IsPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, A i j = A j i) ∧
  (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)

/-- SPD implies PSD. -/
lemma isSymPosDef_imp_isPosSemiDef (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    IsPosSemiDef n A := by
  constructor
  · exact hSPD.1
  · intro x
    by_cases hx : ∃ i, x i ≠ 0
    · exact le_of_lt (hSPD.2 x hx)
    · push_neg at hx
      have : ∀ i j : Fin n, x i * A i j * x j = 0 := by
        intro i j; simp [hx i]
      simp [this]

-- ============================================================
-- §10.3  Pivoted Cholesky factorization
-- ============================================================

/-- **Pivoted Cholesky factorization** for rank-r PSD matrices.

    Π^T A Π = R^T R where Π is a permutation matrix and
    R = [R₁₁ R₁₂; 0 0] with R₁₁ being r × r upper triangular
    with positive diagonal.

    This captures the structure from Theorem 10.9 equation (10.11). -/
structure PivotedCholeskySpec (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (r : ℕ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- R is upper triangular. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0
  /-- First r diagonal entries are positive. -/
  R_diag_pos : ∀ i : Fin n, i.val < r → 0 < R i i
  /-- Last n-r rows of R are zero (rank deficiency). -/
  R_rank_zero : ∀ i j : Fin n, r ≤ i.val → R i j = 0
  /-- Π^T A Π = R^T R. -/
  product_eq : ∀ i j : Fin n,
    ∑ k : Fin n, R k i * R k j = A (σ i) (σ j)

/-- **Positive semidefiniteness is invariant under simultaneous
    permutation** (Theorem 10.9(b) foundation): if `σ` is a permutation,
    `(i, j) ↦ A (σ i) (σ j)` is PSD whenever `A` is — the permuted
    quadratic form at `x` is the original form at `x ∘ σ⁻¹`. -/
lemma isPosSemiDef_perm (n : ℕ) (A : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (hσ : IsPermutation n σ)
    (hPSD : IsPosSemiDef n A) :
    IsPosSemiDef n (fun i j => A (σ i) (σ j)) := by
  obtain ⟨σinv, hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hσ
  refine ⟨fun i j => hPSD.1 (σ i) (σ j), ?_⟩
  intro x
  have h1 : ∀ (F : Fin n → ℝ), ∑ i : Fin n, F i = ∑ i : Fin n, F (σ i) :=
    fun F => (Fintype.sum_bijective σ hσ (fun i => F (σ i)) F
      (fun i => rfl)).symm
  have h := hPSD.2 (fun k => x (σinv k))
  calc (0:ℝ)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          x (σinv i) * A i j * x (σinv j) := h
    _ = ∑ i : Fin n, ∑ j : Fin n,
          x (σinv (σ i)) * A (σ i) (σ j) * x (σinv (σ j)) := by
        rw [h1 (fun i => ∑ j : Fin n,
          x (σinv i) * A i j * x (σinv j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [h1 (fun j => x (σinv (σ i)) * A (σ i) j * x (σinv j))]
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * A (σ i) (σ j) * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hleft i, hleft j]

/-- **Complete-pivoting selection step** (Theorem 10.9(b) / §10.3): when
    some diagonal entry of a PSD matrix is positive, a transposition
    brings a largest diagonal entry to the pivot position; the permuted
    matrix has a positive leading pivot dominating every diagonal entry. -/
lemma psd_pivot_selection {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hnz : ∃ i, 0 < A i i) :
    ∃ σ : Fin (m + 1) → Fin (m + 1), IsPermutation (m + 1) σ ∧
      0 < A (σ 0) (σ 0) ∧
      ∀ i : Fin (m + 1), A (σ i) (σ i) ≤ A (σ 0) (σ 0) := by
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (m + 1))) (fun i => A i i)
    ⟨0, Finset.mem_univ 0⟩
  obtain ⟨w, hw⟩ := hnz
  refine ⟨⇑(Equiv.swap 0 t), (Equiv.swap 0 t).bijective, ?_, ?_⟩
  · rw [Equiv.swap_apply_left]
    exact lt_of_lt_of_le hw (ht w (Finset.mem_univ w))
  · intro i
    rw [Equiv.swap_apply_left]
    exact ht _ (Finset.mem_univ _)

/-- Two-point evaluation of the quadratic form: for `x` supported on
    `{i, j}` with `i ≠ j`, `xᵀAx = t²·a_ii + ts·(a_ij + a_ji) + s²·a_jj`. -/
private lemma quadForm_two_point {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (t s : ℝ) :
    ∑ k : Fin n, ∑ l : Fin n,
      (if k = i then t else if k = j then s else 0) * A k l *
      (if l = i then t else if l = j then s else 0) =
    t ^ 2 * A i i + t * s * (A i j + A j i) + s ^ 2 * A j j := by
  have hrow : ∀ k : Fin n,
      ∑ l : Fin n, (if k = i then t else if k = j then s else 0) * A k l *
        (if l = i then t else if l = j then s else 0) =
      (if k = i then t else if k = j then s else 0) *
        (A k i * t + A k j * s) := by
    intro k
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
      (Finset.mem_univ j) hij ?_]
    · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
      ring
    · intro l _ hl
      rcases hl with ⟨hli, hlj⟩
      simp [hli, hlj]
  rw [Finset.sum_congr rfl fun k _ => hrow k]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
    (Finset.mem_univ j) hij ?_]
  · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
    ring
  · intro k _ hk
    rcases hk with ⟨hki, hkj⟩
    simp [hki, hkj]

/-- **All diagonal entries zero forces the zero matrix** for PSD matrices
    (Theorem 10.9(b) recursion, termination case): with every `a_ii = 0`,
    the two-point quadratic form reduces to `2ts·a_ij ≥ 0` for all
    `t, s`, so every entry vanishes. -/
lemma psd_all_diag_zero {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (hdiag : ∀ i, A i i = 0) :
    ∀ i j : Fin n, A i j = 0 := by
  intro i j
  by_cases hij : i = j
  · rw [hij]; exact hdiag j
  · have hpos := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then 1 else 0)
    have hneg := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then (-1) else 0)
    rw [quadForm_two_point A i j hij 1 1] at hpos
    rw [quadForm_two_point A i j hij 1 (-1)] at hneg
    have hsym := hPSD.1 i j
    rw [hdiag i, hdiag j] at hpos hneg
    nlinarith [hpos, hneg, hsym]

/-- Extend a permutation of `Fin m` to `Fin (m+1)` fixing `0` and acting
    on successors (Theorem 10.9(b) recursion: composing the tail stage's
    permutation with the current pivot transposition). -/
noncomputable def extendPerm {m : ℕ} (σ' : Fin m → Fin m) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (σ' i).succ)

@[simp] lemma extendPerm_zero {m : ℕ} (σ' : Fin m → Fin m) :
    extendPerm σ' 0 = 0 := rfl

@[simp] lemma extendPerm_succ {m : ℕ} (σ' : Fin m → Fin m) (i : Fin m) :
    extendPerm σ' i.succ = (σ' i).succ := by
  unfold extendPerm
  rw [Fin.cases_succ]

/-- Extension preserves the permutation property. -/
lemma extendPerm_isPermutation {m : ℕ} (σ' : Fin m → Fin m)
    (hσ' : IsPermutation m σ') :
    IsPermutation (m + 1) (extendPerm σ') := by
  obtain ⟨inv', hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hσ'
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Fin.cases 0 (fun i => (inv' i).succ), ?_, ?_⟩
  · intro x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro i
      rw [extendPerm_succ]
      simp only [Fin.cases_succ]
      rw [hleft i]
  · intro x
    refine Fin.cases ?_ ?_ x
    · rfl
    · intro i
      simp only [Fin.cases_succ]
      rw [extendPerm_succ, hright i]

-- ============================================================
-- §10.3  Theorem 10.9: PSD Cholesky existence (helpers)
-- ============================================================

/-- Diagonal entry of a PSD matrix is nonnegative. -/
private lemma psd_diag_nonneg {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (i : Fin (m + 1)) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  suffices hs : ∑ k₁ : Fin (m + 1), ∑ k₂ : Fin (m + 1),
      (if k₁ = i then 1 else 0) * A k₁ k₂ * (if k₂ = i then 1 else 0) = A i i by linarith
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
      Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp)]
  simp

/-- If a PSD matrix has A_{00} = 0, then the entire first row is zero.

    Proof: the quadratic form x^T A x evaluated at x = e_0 + t·e_{j+1}
    gives 2t·A_{0,j+1} + t²·A_{j+1,j+1} ≥ 0 for all t, forcing A_{0,j+1} = 0. -/
private lemma psd_zero_diag_row_zero {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (h00 : A 0 0 = 0) (j : Fin m) :
    A 0 j.succ = 0 := by
  set a := A 0 j.succ
  set d := A j.succ j.succ
  have hd_nn : 0 ≤ d := psd_diag_nonneg hPSD j.succ
  -- Key: for all t, 0 ≤ 2ta + t²d (= x^T A x for x = e_0 + t·e_{j+1})
  suffices key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * d by
    by_cases hd : d = 0
    · have h1 := key 1; have h2 := key (-1); nlinarith
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd)
      have h := key (-a / d)
      have hcalc : 2 * (-a / d) * a + (-a / d) ^ 2 * d = -(a ^ 2 / d) := by
        field_simp; ring
      rw [hcalc] at h
      have h_pos : 0 ≤ a ^ 2 / d := div_nonneg (sq_nonneg a) (le_of_lt hd_pos)
      have h_zero : a ^ 2 / d = 0 := le_antisymm (by linarith) h_pos
      have ha_sq : a ^ 2 = 0 := by
        by_contra h_ne
        exact absurd h_zero (ne_of_gt (div_pos (lt_of_le_of_ne (sq_nonneg a)
          (Ne.symm h_ne)) hd_pos))
      exact sq_eq_zero_iff.mp ha_sq
  -- Prove: x^T A x = 2ta + t²d for suitable x
  intro t
  have hpsd := hPSD.2 (fun k => if k = (0 : Fin (m + 1)) then 1
    else if k = j.succ then t else 0)
  suffices heval : ∑ i : Fin (m + 1), ∑ k : Fin (m + 1),
      (if i = (0 : Fin (m + 1)) then 1 else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then 1 else if k = j.succ then t else 0) =
      2 * t * a + t ^ 2 * d by linarith
  -- Inner sum: ∑_k A_{ik} · x_k = A_{i,0} + t · A_{i,j+1}
  have inner : ∀ i : Fin (m + 1), ∑ k : Fin (m + 1), A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      A i 0 + t * A i j.succ := by
    intro i; rw [Fin.sum_univ_succ]; simp only [ite_true, mul_one]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                  ite_false, ite_true]; ring
    · intro b _ hb
      have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Factor x_i out and apply inner sum
  simp_rw [show ∀ (i k : Fin (m + 1)),
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) *
      (A i k * (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0))
    from fun i k => by ring]
  simp_rw [← Finset.mul_sum, inner]
  -- Outer sum: ∑_i x_i · (A_{i,0} + t·A_{i,j+1})
  rw [Fin.sum_univ_succ]
  simp only [ite_true, one_mul]
  rw [Finset.sum_eq_single j]
  · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                ite_false, ite_true]
    rw [h00, hPSD.1 j.succ 0]; ring
  · intro b _ hb
    have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
    simp [Fin.succ_ne_zero, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Schur complement of PSD is PSD** (Higham §10.3, Lemma 10.11).

    If A is positive semidefinite with A₀₀ > 0, then the Schur complement
    S = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂ is also positive semidefinite.

    Proof: y^T S y = x^T A x where x₀ = −(a^T y)/a₁₁, x_{i+1} = yᵢ.
    Since A is PSD, x^T A x ≥ 0, so y^T S y ≥ 0 for all y. -/
lemma schur_psd {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (ha₁₁ : 0 < A 0 0) :
    IsPosSemiDef m (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) := by
  have ha_ne : A 0 0 ≠ 0 := ne_of_gt ha₁₁
  constructor
  · intro i j; show A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0 =
      A j.succ i.succ - A 0 j.succ * A 0 i.succ / A 0 0
    rw [hPSD.1 i.succ j.succ, hPSD.1 0 i.succ, hPSD.1 0 j.succ]; ring
  · intro y
    set t := ∑ j : Fin m, A 0 j.succ * y j
    set Q := ∑ i : Fin m, ∑ j : Fin m, y i * A i.succ j.succ * y j
    set x : Fin (m + 1) → ℝ := Fin.cons (-t / A 0 0) y
    have hpsd_x := hPSD.2 x
    suffices heq :
        ∑ i : Fin m, ∑ j : Fin m, y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
    have ht' : ∑ i : Fin m, y i * A 0 i.succ = t := by
      show ∑ i, y i * A 0 i.succ = ∑ j, A 0 j.succ * y j; congr 1; ext i; ring
    -- LHS = Q - t²/A₀₀
    have lhs_eq : ∑ i : Fin m, ∑ j : Fin m, y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        Q - t * t / A 0 0 := by
      simp_rw [show ∀ (i j : Fin m), y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
          y i * A i.succ j.succ * y j -
          (y i * A 0 i.succ) * (A 0 j.succ * y j) / A 0 0
          from fun i j => by ring]
      simp_rw [Finset.sum_sub_distrib]
      congr 1
      simp_rw [← Finset.sum_div]
      congr 1
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      rw [ht']
    -- RHS = Q - t²/A₀₀
    have rhs_eq : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j =
        Q - t * t / A 0 0 := by
      rw [Fin.sum_univ_succ]
      simp only [x, Fin.cons_zero, Fin.cons_succ]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      simp_rw [show ∀ j : Fin m, (-t / A 0 0) * A 0 j.succ * y j =
          (-t / A 0 0) * (A 0 j.succ * y j) from fun j => by ring]
      rw [← Finset.mul_sum]
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ,
        show ∀ i : Fin m, A i.succ 0 = A 0 i.succ from fun i => hPSD.1 i.succ 0]
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ht']
      field_simp; ring
    rw [lhs_eq, rhs_eq]

-- ============================================================
-- §10.3  Theorem 10.9: PSD Cholesky existence
-- ============================================================

/-- **PSD Cholesky existence** (Higham §10.3, Theorem 10.9, part a).

    Every positive semidefinite matrix has a factorization A = R^T R
    with R upper triangular and nonnegative diagonal.

    Proof by induction on n using the Schur complement:
    - If A_{00} = 0: first row/column is zero, recurse on submatrix.
    - If A_{00} > 0: form Schur complement S (PSD), recurse,
      assemble R = [[√a₁₁, a^T/√a₁₁], [0, R₁]]. -/
theorem psd_cholesky_existence (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i,
           fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    have ha₁₁_nn : 0 ≤ A 0 0 := psd_diag_nonneg hPSD 0
    by_cases ha₁₁ : A 0 0 = 0
    · -- Case A₀₀ = 0: first row/column is zero
      have hrow : ∀ j : Fin m, A 0 j.succ = 0 := psd_zero_diag_row_zero hPSD ha₁₁
      have hcol : ∀ i : Fin m, A i.succ 0 = 0 := fun i => by rw [hPSD.1]; exact hrow i
      -- Lower-right submatrix is PSD
      set B : Fin m → Fin m → ℝ := fun i j => A i.succ j.succ
      have hB_psd : IsPosSemiDef m B := by
        constructor
        · intro i j; exact hPSD.1 i.succ j.succ
        · intro y
          set x : Fin (m + 1) → ℝ := Fin.cons 0 y
          have h := hPSD.2 x
          suffices heq : ∑ i : Fin m, ∑ j : Fin m, y i * B i j * y j =
              ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
          rw [Fin.sum_univ_succ]
          simp only [x, Fin.cons_zero, zero_mul, Finset.sum_const_zero, zero_add]
          simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, B]
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih B hB_psd
      -- R: first row all zero, rest = R₁
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then 0
        else if hj : j = 0 then 0
        else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p = 0 := fun p => by simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi]; exact hR₁_diag _
      · -- product_eq
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [ha₁₁]
        · subst hi; simp only [dite_true]; simp [hj]
          have := hrow (j.pred hj)
          rw [Fin.succ_pred] at this; exact this.symm
        · subst hj; simp only [dite_true]; simp [hi]
          have := hcol (i.pred hi)
          rw [Fin.succ_pred] at this; exact this.symm
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [B, Fin.succ_pred] at hih
          linarith
    · -- Case A₀₀ > 0: Schur complement induction
      have ha₁₁_pos : 0 < A 0 0 := lt_of_le_of_ne ha₁₁_nn (Ne.symm ha₁₁)
      set S : Fin m → Fin m → ℝ := fun i j =>
        A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
      have hS_psd := schur_psd hPSD ha₁₁_pos
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih S hS_psd
      set sa := Real.sqrt (A 0 0)
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos ha₁₁_pos
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = A 0 0 := Real.mul_self_sqrt (le_of_lt ha₁₁_pos)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then
          if hj : j = 0 then sa else A 0 j / sa
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else A 0 p / sa := by
        intro p; simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · subst hi; simp; exact le_of_lt hsa_pos
        · simp [hi]; exact hR₁_diag _
      · -- product_eq (same structure as cholesky_existence)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [hsa_sq]
        · subst hi; simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj; simp [hi, hPSD.1 i 0, hsa_ne]
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [S, Fin.succ_pred] at hih
          have h1 : A 0 i / sa * (A 0 j / sa) = A 0 i * A 0 j / A 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          linarith

/-- **Theorem 10.9(b), constructive core** (Higham §10.3, equation
    (10.11)): every real PSD matrix admits a pivoted Cholesky
    factorization `Πᵀ A Π = RᵀR` in the displayed rank-truncated form,
    with the permutation produced by greedy complete pivoting and `r`
    the number of positive pivots encountered.  Identification of `r`
    with the matrix rank is left as a separate row over Mathlib's rank. -/
theorem psd_pivoted_cholesky_exists (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0, Function.bijective_id,
        fun i j _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i j _ => rfl, fun i j => ?_⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, _⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
        fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
        fun i j => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring

/-- **Schur diagonal domination** (equation (10.13) foundation): each
    Schur-complement diagonal entry is at most the corresponding original
    diagonal entry, hence — under the complete-pivoting choice — at most
    the current pivot.  This is the monotonicity that propagates the
    per-stage maximality into the (10.13) display. -/
lemma schur_diag_le_pivot {m : ℕ} (B : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hB00 : 0 < B 0 0)
    (hmax : ∀ i : Fin (m + 1), B i i ≤ B 0 0) (i : Fin m) :
    B i.succ i.succ - B 0 i.succ * B 0 i.succ / B 0 0 ≤ B 0 0 := by
  have hsub : 0 ≤ B 0 i.succ * B 0 i.succ / B 0 0 :=
    div_nonneg (mul_self_nonneg _) hB00.le
  linarith [hmax i.succ]

/-- **Column-tail identity for the pivoted factor** (equation (10.13)
    foundation, spec level): the tail of a squared column of `R` from row
    `k` down equals the permuted diagonal entry minus the head — i.e. the
    stage-`k` Schur diagonal in factored form.  Combined with the
    stage-domination invariant this yields the display (10.13). -/
lemma pivoted_spec_column_split {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (k j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
      R i j ^ 2) =
    A (σ j) (σ j) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2 := by
  have hprod := hspec.product_eq j j
  have hsq : ∑ i : Fin n, R i j * R i j = ∑ i : Fin n, R i j ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsq] at hprod
  have hsplit : ∑ i : Fin n, R i j ^ 2 =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k.val) (fun i => R i j ^ 2)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp
  linarith [hprod, hsplit]

/-- The leading diagonal entry of a pivoted factor squares to the
    permuted leading diagonal of `A` (product equation at `(0,0)` with
    upper triangularity). -/
lemma pivoted_spec_head_sq {m : ℕ} {A R : Fin (m + 1) → Fin (m + 1) → ℝ}
    {σ : Fin (m + 1) → Fin (m + 1)} {r : ℕ}
    (hspec : PivotedCholeskySpec (m + 1) A R σ r) :
    R 0 0 * R 0 0 = A (σ 0) (σ 0) := by
  have h := hspec.product_eq 0 0
  rw [Fin.sum_univ_succ] at h
  rw [show ∑ i : Fin m, R i.succ 0 * R i.succ 0 = 0 from
    Finset.sum_eq_zero fun i _ => by
      rw [hspec.R_upper i.succ 0 (by simp), zero_mul]] at h
  linarith

/-- Diagonal entries of a pivoted factor are nonnegative. -/
lemma pivoted_spec_diag_nonneg {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (i : Fin n) :
    0 ≤ R i i := by
  rcases Nat.lt_or_ge i.val r with h | h
  · exact (hspec.R_diag_pos i h).le
  · rw [hspec.R_rank_zero i i h]

/-- **Theorem 10.9(b) with the complete-pivoting invariant**: the greedy
    construction additionally yields nonincreasing factor diagonal —
    `R l l ≤ R k k` for `k ≤ l` — the per-stage maximality that together
    with `pivoted_spec_column_split` gives the display (10.13). -/
theorem psd_pivoted_cholesky_exists_cp (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k l : Fin n, k.val ≤ l.val → R l l ≤ R k k := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k l _ => le_rfl⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, hmono⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      -- the tail's leading diagonal is bounded by the pivot root
      have hR₁_le_sa : ∀ i : Fin m, R₁ i i ≤ sa := by
        intro i
        rcases Nat.eq_zero_or_pos m with hm | hm
        · exact absurd i.isLt (by omega)
        · have h0m : (0 : ℕ) < m := hm
          have hhead : R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ =
              S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) := by
            have h := hspec.product_eq ⟨0, h0m⟩ ⟨0, h0m⟩
            rw [show ∑ k : Fin m, R₁ k ⟨0, h0m⟩ * R₁ k ⟨0, h0m⟩ =
                R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ from ?_] at h
            · exact h
            · rw [Finset.sum_eq_single ⟨0, h0m⟩]
              · intro b _ hb
                rw [hspec.R_upper b ⟨0, h0m⟩ (by
                  have hb0 : b.val ≠ 0 := fun h0 => hb (Fin.ext h0)
                  show 0 < b.val
                  omega), zero_mul]
              · intro habs
                exact absurd (Finset.mem_univ _) habs
          have hSmax : S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) ≤ B 0 0 :=
            schur_diag_le_pivot B hB00 (fun i => hτ_max i) _
          have hi_le : R₁ i i ≤ R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ :=
            hmono ⟨0, h0m⟩ i (by simp)
          have hnn := pivoted_spec_diag_nonneg hspec ⟨0, h0m⟩
          nlinarith [pivoted_spec_diag_nonneg hspec i, hsa_sq, hsa_pos]
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => ?_⟩, fun k l hkl => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      · -- diagonal monotonicity
        simp only [hRdef]
        by_cases hk : k = 0
        · subst hk
          by_cases hl : l = 0
          · subst hl; simp
          · simp only [dif_neg hl]
            exact hR₁_le_sa _
        · have hlk : l ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hl0 : l.val = 0 := by simp [h0]
            omega
          simp only [dif_neg hk, dif_neg hlk]
          exact hmono _ _ (by
            have := Fin.val_pred k hk
            have := Fin.val_pred l hlk
            omega)

/-- Reindex a succ-tail filter sum over `Fin (m+1)` to a tail filter sum
    over `Fin m`. -/
private lemma sum_filter_succ_tail {m : ℕ} (k₀ : ℕ)
    (f : Fin (m + 1) → ℝ) :
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val), f i) =
    ∑ i₀ ∈ Finset.univ.filter (fun i₀ : Fin m => k₀ ≤ i₀.val),
      f i₀.succ := by
  have himg : (Finset.univ.filter
      (fun i₀ : Fin m => k₀ ≤ i₀.val)).image Fin.succ =
      Finset.univ.filter (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨i₀, hi₀, rfl⟩
      simp only [Fin.val_succ]
      omega
    · intro hi
      have hne : i ≠ 0 := by
        intro h0
        rw [h0] at hi
        simp at hi
      refine ⟨i.pred hne, ?_, Fin.succ_pred i hne⟩
      have := Fin.val_pred i hne
      omega
  rw [← himg, Finset.sum_image
    (fun a _ b _ h => Fin.succ_injective m h)]

/-- **Theorem 10.9(b) with the (10.13) column-tail invariant**: the greedy
    complete-pivoting construction yields, beyond the pivoted certificate,
    the stage-wise column-tail domination
    `∑_{i ≥ k} r_ij² ≤ r_kk²` for `k ≤ j` — precisely the content of the
    display (10.13). -/
theorem psd_pivoted_cholesky_exists_tail (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k j : Fin n, k.val ≤ j.val →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
          R i j ^ 2) ≤ R k k ^ 2 := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k j _ => by simp⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, htail⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      have hproduct : ∀ i j : Fin (m + 1),
          ∑ p : Fin (m + 1), R p i * R p j =
          B (extendPerm σ' i) (extendPerm σ' j) := by
        intro i j
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => hproduct i j⟩, fun k j hkj => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · -- column-tail domination (the (10.13) invariant)
        by_cases hk : k = 0
        · subst hk
          have hfilter : Finset.univ.filter
              (fun i : Fin (m + 1) => (0 : Fin (m + 1)).val ≤ i.val) =
              Finset.univ := by
            ext i; simp
          rw [hfilter]
          have hsum : ∑ i : Fin (m + 1), R i j ^ 2 =
              B (extendPerm σ' j) (extendPerm σ' j) := by
            rw [← hproduct j j]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hsum]
          have hR00 : R 0 0 = sa := by rw [hR0 0]; simp
          rw [hR00]
          calc B (extendPerm σ' j) (extendPerm σ' j) ≤ B 0 0 :=
              hτ_max (extendPerm σ' j)
            _ = sa ^ 2 := by rw [← hsa_sq]; ring
        · have hj0 : j ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hjv : j.val = 0 := by simp [h0]
            omega
          have hkval : k.val = (k.pred hk).val + 1 := by
            have := Fin.val_pred k hk
            have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
            omega
          have hfeq : Finset.univ.filter
              (fun i : Fin (m + 1) => k.val ≤ i.val) =
              Finset.univ.filter
              (fun i : Fin (m + 1) => (k.pred hk).val + 1 ≤ i.val) := by
            apply Finset.filter_congr
            intro i _
            constructor <;> intro h <;> omega
          rw [hfeq, sum_filter_succ_tail (k.pred hk).val
            (fun i => R i j ^ 2)]
          have hterm : ∀ i₀ : Fin m, R i₀.succ j ^ 2 =
              R₁ i₀ (j.pred hj0) ^ 2 := by
            intro i₀
            rw [hRs i₀ j, dif_neg hj0]
          rw [Finset.sum_congr rfl fun i₀ _ => hterm i₀]
          have hkk : R k k = R₁ (k.pred hk) (k.pred hk) := by
            conv_lhs => rw [← Fin.succ_pred k hk]
            rw [hRs (k.pred hk) (k.pred hk).succ,
              dif_neg (Fin.succ_ne_zero _), Fin.pred_succ]
          rw [hkk]
          exact htail (k.pred hk) (j.pred hj0) (by
            have := Fin.val_pred j hj0
            have := Fin.val_pred k hk
            omega)

/-- **Rank invariance of the pivoted certificate** (Theorem 10.9(b),
    `r = rank` bridge, part 1): the matrix rank of `A` equals the rank of
    the pivoted factor `R` — `rank A = rank(ΠᵀAΠ) = rank(RᵀR) = rank R`.
    The remaining identification `rank R = r` (triangular rank count) is
    a separate row. -/
theorem pivoted_spec_rank_eq {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) :
    (Matrix.of A).rank = (Matrix.of R).rank := by
  let eσ : Fin n ≃ Fin n := Equiv.ofBijective σ hspec.perm
  have hsub : (Matrix.of A).submatrix ⇑eσ ⇑eσ =
      (Matrix.of R).transpose * Matrix.of R := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply]
    show A (σ i) (σ j) = ∑ k : Fin n, R k i * R k j
    rw [← hspec.product_eq i j]
  calc (Matrix.of A).rank
      = ((Matrix.of A).submatrix ⇑eσ ⇑eσ).rank :=
        (Matrix.rank_submatrix (Matrix.of A) eσ eσ).symm
    _ = ((Matrix.of R).transpose * Matrix.of R).rank := by rw [hsub]
    _ = (Matrix.of R).rank :=
        Matrix.rank_transpose_mul_self (Matrix.of R)

/-- **The leading `r × r` block of a pivoted factor is a determinant
    unit** (Theorem 10.9(b), `rank R = r` bridge, `≥` side): upper
    triangular with positive diagonal, so its determinant is the product
    of the positive pivots. -/
theorem pivoted_leading_block_isUnit_det {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    IsUnit (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det := by
  have hBT : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).BlockTriangular id := by
    intro i j hij
    exact hspec.R_upper _ _ hij
  rw [Matrix.det_of_upperTriangular hBT]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (hspec.R_diag_pos ⟨i.val, by omega⟩ i.isLt).ne'

/-- **Triangular rank count** (Theorem 10.9(b), `r = rank` bridge,
    part 2): the pivoted factor has matrix rank exactly `r` — the zero
    rows give `≤` and the unit leading block gives `≥`, both through
    selection-matrix factorizations and `rank_mul_le`. -/
theorem pivoted_spec_rank_R {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of R).rank = r := by
  set Rtop : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k j => R ⟨k.val, by omega⟩ j) with hRtop
  set E : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun i k => if i.val = k.val then (1:ℝ) else 0) with hE
  set E' : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k i => if k.val = i.val then (1:ℝ) else 0) with hE'
  set F : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun j k => if j.val = k.val then (1:ℝ) else 0) with hF
  have hfac1 : Matrix.of R = E * Rtop := by
    ext i j
    show R i j = ∑ k : Fin r,
      (if i.val = k.val then (1:ℝ) else 0) * R ⟨k.val, by omega⟩ j
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin r)]
      · rw [if_pos rfl, one_mul]
      · intro b _ hb
        rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hspec.R_rank_zero i j (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by omega), zero_mul]
  have hfac2 : Rtop = E' * Matrix.of R := by
    ext k j
    show R ⟨k.val, by omega⟩ j = ∑ i : Fin n,
      (if k.val = i.val then (1:ℝ) else 0) * R i j
    rw [Finset.sum_eq_single (⟨k.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac3 : Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = Rtop * F := by
    ext k k'
    show R ⟨k.val, by omega⟩ ⟨k'.val, by omega⟩ = ∑ j : Fin n,
      R ⟨k.val, by omega⟩ j * (if j.val = k'.val then (1:ℝ) else 0)
    rw [Finset.sum_eq_single (⟨k'.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hMrank : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).rank = r := by
    rw [Matrix.rank_of_isUnit _
      ((Matrix.isUnit_iff_isUnit_det _).mpr
        (pivoted_leading_block_isUnit_det hspec hr))]
    simp
  have h1 : (Matrix.of R).rank ≤ Rtop.rank := by
    rw [hfac1]
    exact Matrix.rank_mul_le_right E Rtop
  have h2 : Rtop.rank ≤ (Matrix.of R).rank := by
    rw [hfac2]
    exact Matrix.rank_mul_le_right E' (Matrix.of R)
  have h3 : r ≤ Rtop.rank := by
    have hle := Matrix.rank_mul_le_left Rtop F
    rw [← hfac3, hMrank] at hle
    exact hle
  have h4 : Rtop.rank ≤ r := by
    have := Matrix.rank_le_card_height Rtop
    simpa using this
  omega

/-- **Theorem 10.9(b), rank identification**: for any pivoted certificate
    with `r ≤ n`, the parameter `r` is the matrix rank of `A` — closing
    the "positive semidefinite of rank r" reading of the source row. -/
theorem pivoted_spec_rank_eq_r {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of A).rank = r := by
  rw [pivoted_spec_rank_eq hspec, pivoted_spec_rank_R hspec hr]

-- ============================================================
-- §10.3  Theorem 10.9(b): SPD → PivotedCholeskySpec (full rank)
-- ============================================================

/-- **SPD Cholesky as pivoted Cholesky** (Higham §10.3, Theorem 10.9, part b, full rank case).

    For SPD matrices, the Cholesky factorization from Theorem 10.1 satisfies
    PivotedCholeskySpec with identity permutation and rank r = n.
    All diagonal entries are strictly positive and no rows are zero. -/
theorem spd_pivoted_cholesky (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      PivotedCholeskySpec n A R id n := by
  obtain ⟨R, hR⟩ := cholesky_existence n A hSPD
  exact ⟨R,
    { perm := Function.bijective_id
      R_upper := hR.R_upper
      R_diag_pos := fun i _ => hR.R_diag_pos i
      R_rank_zero := fun i _ hri => absurd hri (by omega)
      product_eq := fun i j => hR.product_eq i j }⟩

-- ============================================================
-- §10.3  Schur complement
-- ============================================================

/-- **Schur complement** of the (1,1) block in a partitioned matrix.

    For a matrix partitioned as [A₁₁ A₁₂; A₂₁ A₂₂]:
      S_k(A) = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂

    We represent this abstractly: given A₁₁⁻¹ as a hypothesis,
    the Schur complement maps indices (i, j) with i, j ≥ k to:
      S(i,j) = A(i,j) − ∑_{s<k} ∑_{t<k} A(i,s) · A₁₁⁻¹(s,t) · A(t,j) -/
noncomputable def schurComplement (n k : ℕ) (A A11_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ s : Fin n, ∑ t : Fin n,
      (if s.val < k ∧ t.val < k then A i s * A11_inv s t * A t j else 0)

-- ============================================================
-- §10.3  Lemma 10.10: Schur complement perturbation
-- ============================================================


/-- **Resolvent identity for the perturbed leading block** (Lemma 10.10
    setup): if `M` is a left inverse of `A₁₁` and `X` a right... — more
    precisely, if `M * A₁₁ = 1` and `(A₁₁ + E₁₁) * X = 1`, then
    `X = M − M E₁₁ X` exactly. This is the identity that makes the
    Schur-complement perturbation expansion pure algebra. -/
lemma schur_resolvent_from_inverses {k : ℕ}
    (M X A11 E11 : Matrix (Fin k) (Fin k) ℝ)
    (hM : M * A11 = 1) (hXi : (A11 + E11) * X = 1) :
    X = M - M * E11 * X := by
  have h : M * ((A11 + E11) * X) = M := by rw [hXi, mul_one]
  rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hM,
    Matrix.one_mul, ← Matrix.mul_assoc] at h
  linear_combination (norm := abel) h

/-- **First-order split of the perturbed Schur complement** (Lemma 10.10
    engine): with the perturbed leading-block inverse written as
    `X = M − Y`, the perturbed Schur complement decomposes exactly into
    the unperturbed one, the `E`-linear part, and a remainder carrying
    `Y` (which is second order once `Y = M E₁₁ X`). -/
lemma schur_perturbation_split {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X Y : Matrix (Fin k) (Fin k) ℝ) (hX : X = M - Y) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      ((A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12)
        + (-(E21 * M * E12) + (A21 + E21) * Y * (A12 + E12))) := by
  subst hX
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **One re-expansion of the resolvent inside the remainder**: the
    leading remainder term regains Higham's second-order form. -/
lemma schur_remainder_reexpand {k m : ℕ}
    (A21 : Matrix (Fin m) (Fin k) ℝ) (A12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    A21 * (M * E11 * X) * A12 =
      A21 * (M * E11 * M) * A12
        - A21 * (M * E11 * (M * E11 * X)) * A12 := by
  conv_lhs => rw [hX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- **Lemma 10.10, exact form (display (10.16))**: for the perturbed
    block matrix `A + E` with leading-block inverses related by the
    resolvent identity (`schur_resolvent_from_inverses`), the perturbed
    Schur complement equals the unperturbed one plus Higham's
    first-order term
    `Ē = E₂₂ − E₂₁ M A₁₂ − A₂₁ M E₁₂ + A₂₁ M E₁₁ M A₁₂`
    (with `W = M A₁₂`, `Wᵀ = A₂₁ M` for symmetric `A` this is
    `E₂₂ − E₂₁ W − Wᵀ E₁₂ + Wᵀ E₁₁ W`) plus an explicit remainder in
    which every term carries two `E`-factors — the `O(‖E‖²)` of the
    source, here exact rather than asymptotic. -/
theorem schur_perturbation_exact {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      (A22 - A21 * M * A12)
      + (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
      + (-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) := by
  rw [schur_perturbation_split A21 E21 A12 E12 A22 E22 M X
    (M * E11 * X) hX]
  have hre := schur_remainder_reexpand A21 A12 M X E11 hX
  simp only [Matrix.add_mul, Matrix.mul_add] at *
  rw [hre]
  abel

/-- Entrywise bound for a matrix product from entrywise bounds on the
    factors. -/
lemma entrywise_matMul_le {a b c : ℕ}
    (F : Matrix (Fin a) (Fin b) ℝ) (G : Matrix (Fin b) (Fin c) ℝ)
    (f g : ℝ) (hf : 0 ≤ f)
    (hF : ∀ i j, |F i j| ≤ f) (hG : ∀ i j, |G i j| ≤ g) :
    ∀ (i : Fin a) (j : Fin c), |(F * G) i j| ≤ (b : ℝ) * f * g := by
  intro i j
  rw [Matrix.mul_apply]
  calc |∑ s : Fin b, F i s * G s j|
      ≤ ∑ s : Fin b, |F i s * G s j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Fin b, f * g := Finset.sum_le_sum fun s _ => by
        rw [abs_mul]
        exact mul_le_mul (hF i s) (hG s j) (abs_nonneg _) hf
    _ = (b : ℝ) * (f * g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (b : ℝ) * f * g := by ring

/-- **Lemma 10.10, second-order remainder bound**: the exact remainder of
    `schur_perturbation_exact` is entrywise `O(ε²)` — bounded by an
    explicit polynomial in the entrywise bounds `α` (of the off-diagonal
    blocks of `A`), `μ` (of `M = A₁₁⁻¹`), `χ` (of the perturbed inverse
    `X`), times `ε²`. This is the honest content of the source's
    `O(‖E‖²)`. -/
theorem schur_perturbation_remainder_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ χ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) (hX : ∀ i j, |X i j| ≤ χ) :
    ∀ (i j : Fin m),
      |(-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) i j| ≤
      ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
        + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
        * ε ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- entrywise bounds on the building blocks
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEnn : (0 : ℝ) ≤ (k : ℝ) * μ * ε := by positivity
  have hMEX : ∀ (p q : Fin k), |((M * E11) * X) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * χ :=
    entrywise_matMul_le (M * E11) X _ χ hMEnn hME hX
  have hMEXnn : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) * μ * ε) * χ := by
    positivity
  -- term 1 : E21 * M * E12
  have hT1a : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1 : ∀ (p q : Fin m), |((E21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε :=
    entrywise_matMul_le (E21 * M) E12 _ ε (by positivity) hT1a hE12
  -- term 2 : A21 * (M*E11*(M*E11*X)) * A12
  have hInner : ∀ (p q : Fin k), |((M * E11) * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le (M * E11) ((M * E11) * X) _ _ hMEnn hME hMEX
  have hT2a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * ((M * E11) * X))) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hInner
  have hT2 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * ((M * E11) * X))) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT2a hA12
  -- term 3 : E21 * (M*E11*X) * A12
  have hT3a : ∀ (p : Fin m) (q : Fin k),
      |(E21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le E21 _ ε _ hε hE21 hMEX
  have hT3 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3a hA12
  -- term 4 : A21 * (M*E11*X) * E12
  have hT4a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEX
  have hT4 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT4a hE12
  -- term 5 : E21 * (M*E11*X) * E12
  have hT5 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT3a hE12
  -- assemble by the triangle inequality
  have h1 := abs_le.mp (hT1 i j)
  have h2 := abs_le.mp (hT2 i j)
  have h3 := abs_le.mp (hT3 i j)
  have h4 := abs_le.mp (hT4 i j)
  have h5 := abs_le.mp (hT5 i j)
  have hsum : ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
      + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
      * ε ^ 2 =
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
          ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      := by ring
  rw [hsum]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2]

/-- PSD diagonal entries are nonnegative (general-`n` public form). -/
lemma isPosSemiDef_diag_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i : Fin n) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  simpa [Finset.sum_ite_eq', Finset.mul_sum] using h

/-- **PSD off-diagonal domination, non-strict form** (Problem 10.1 in
    PSD strength): `|a_ij| ≤ √(a_ii) √(a_jj)`. -/
lemma psd_abs_entry_le_sqrt_diag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i j : Fin n) :
    |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hdj := isPosSemiDef_diag_nonneg A hPSD j
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_nonneg hdi]
    exact (Real.mul_self_sqrt hdi).ge
  · set u : ℝ := Real.sqrt (A i i) with hu
    set w : ℝ := Real.sqrt (A j j) with hw
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = A i i := Real.sq_sqrt hdi
    have hw2 : w ^ 2 = A j j := Real.sq_sqrt hdj
    have hsym := hPSD.1 i j
    have hqf : ∀ t s : ℝ, 0 ≤ t ^ 2 * A i i + t * s * (2 * A i j) +
        s ^ 2 * A j j := by
      intro t s
      have h := hPSD.2 (fun k => if k = i then t else
        if k = j then s else 0)
      rw [quadForm_two_point A i j hij t s] at h
      have h2 : A i j + A j i = 2 * A i j := by rw [← hsym]; ring
      rw [h2] at h
      linarith [h]
    -- zero-diagonal cases force a zero entry
    by_cases hzi : A i i = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf (-(A j j + 1) / (2 * A i j)) 1
        rw [hzi] at h
        have h2 : (-(A j j + 1) / (2 * A i j)) * 1 * (2 * A i j) =
            -(A j j + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    by_cases hzj : A j j = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf 1 (-(A i i + 1) / (2 * A i j))
        rw [hzj] at h
        have h2 : (1 : ℝ) * (-(A i i + 1) / (2 * A i j)) *
            (2 * A i j) = -(A i i + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    -- positive-diagonal case: evaluate at (w, ±u)
    have hupos : 0 < u := Real.sqrt_pos.mpr (lt_of_le_of_ne hdi
      (Ne.symm hzi))
    have hwpos : 0 < w := Real.sqrt_pos.mpr (lt_of_le_of_ne hdj
      (Ne.symm hzj))
    have hq1 := hqf w u
    have hq2 := hqf w (-u)
    rw [abs_le]
    constructor
    · nlinarith [hq1, hu2, hw2, mul_pos hupos hwpos]
    · nlinarith [hq2, hu2, hw2, mul_pos hupos hwpos]

/-- **PSD quadratic form is trace-bounded**:
    `xᵀAx ≤ (∑ᵢ a_ii)(∑ᵢ xᵢ²)` — entrywise domination by
    `√(a_ii a_jj)` plus Cauchy–Schwarz. This turns the trace into a
    computable operator certificate for PSD matrices. -/
lemma psd_quadForm_le_trace {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := by
  have hstep : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      ∑ i : Fin n, ∑ j : Fin n,
        (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have habs : x i * A i j * x j ≤ |x i| * |A i j| * |x j| := by
      calc x i * A i j * x j ≤ |x i * A i j * x j| := le_abs_self _
        _ = |x i| * |A i j| * |x j| := by rw [abs_mul, abs_mul]
    calc x i * A i j * x j ≤ |x i| * |A i j| * |x j| := habs
      _ ≤ |x i| * (Real.sqrt (A i i) * Real.sqrt (A j j)) * |x j| := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (psd_abs_entry_le_sqrt_diag A hPSD i j)
              (abs_nonneg _)) (abs_nonneg _)
      _ = (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) :=
          by ring
  have hsq : ∑ i : Fin n, ∑ j : Fin n,
      (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) =
      (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |x i|) (fun i => Real.sqrt (A i i))
  have hL : ∑ i : Fin n, |x i| ^ 2 = ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  have hR : ∑ i : Fin n, Real.sqrt (A i i) ^ 2 = ∑ i : Fin n, A i i :=
    Finset.sum_congr rfl fun i _ =>
      Real.sq_sqrt (isPosSemiDef_diag_nonneg A hPSD i)
  rw [hL, hR] at hcs
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 :=
        hstep.trans_eq hsq
    _ ≤ (∑ i : Fin n, x i ^ 2) * ∑ i : Fin n, A i i := hcs
    _ = (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := mul_comm _ _

/-- **PSD entries are dominated by the largest diagonal entry**
    (Higham §10.3, the (10.23)/(10.24) termination engine): if every
    diagonal entry of a PSD matrix is at most `d`, every entry is at
    most `d` in absolute value. Applied to the exact trailing Schur
    complement at termination, this converts the pivoted algorithm's
    stopping test `max diag ≤ tol` into the entrywise trailing residual
    bound. -/
lemma psd_abs_entry_le_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (i j : Fin n) :
    |A i j| ≤ d := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hd0 : 0 ≤ d := le_trans hdi (hd i)
  calc |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) :=
        psd_abs_entry_le_sqrt_diag A hPSD i j
    _ ≤ Real.sqrt d * Real.sqrt d :=
        mul_le_mul (Real.sqrt_le_sqrt (hd i))
          (Real.sqrt_le_sqrt (hd j)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = d := Real.mul_self_sqrt hd0

/-- **PSD quadratic form bounded by dimension times the largest
    diagonal** (the normwise reading of the same engine):
    `xᵀAx ≤ n·d·‖x‖₂²` when every `a_ii ≤ d`. -/
lemma psd_quadForm_le_card_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 := by
  have htr : (∑ i : Fin n, A i i) ≤ (n : ℝ) * d := by
    calc ∑ i : Fin n, A i i ≤ ∑ _i : Fin n, d :=
          Finset.sum_le_sum fun i _ => hd i
      _ = (n : ℝ) * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hx : 0 ≤ ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 :=
        psd_quadForm_le_trace A hPSD x
    _ ≤ (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 :=
        mul_le_mul_of_nonneg_right htr hx

/-- **Entrywise bound on Higham's first-order term**: with entrywise
    data `|E| ≤ ε`, `|A₂₁|, |A₁₂| ≤ α`, `|M| ≤ μ`, the first-order term
    of (10.16) satisfies `|Ē i j| ≤ ε (1 + k²αμ)²` — the source's
    `(1 + ‖W‖)²` shape with `k²αμ` the entrywise scale of
    `W = M A₁₂`. -/
lemma schur_first_order_entrywise_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (E22 : Matrix (Fin m) (Fin m) ℝ)
    (M E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε) (hE22 : ∀ i j, |E22 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) :
    ∀ (i j : Fin m),
      |(E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12) i j| ≤
      ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT1 : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1' : ∀ (p q : Fin m), |((E21 * M) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * α :=
    entrywise_matMul_le (E21 * M) A12 _ α (by positivity) hT1 hA12
  have hT2 : ∀ (p : Fin m) (q : Fin k), |(A21 * M) p q| ≤
      (k : ℝ) * α * μ := entrywise_matMul_le A21 M α μ hα hA21 hM
  have hT2' : ∀ (p q : Fin m), |((A21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * μ) * ε :=
    entrywise_matMul_le (A21 * M) E12 _ ε (by positivity) hT2 hE12
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEM : ∀ (p q : Fin k), |((M * E11) * M) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * μ :=
    entrywise_matMul_le (M * E11) M _ μ (by positivity) hME hM
  have hT3 : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * M)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEM
  have hT3' : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * M)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3 hA12
  have h22 := abs_le.mp (hE22 i j)
  have h1 := abs_le.mp (hT1' i j)
  have h2 := abs_le.mp (hT2' i j)
  have h3 := abs_le.mp (hT3' i j)
  have hgoal : ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 =
      ε + (k : ℝ) * ((k : ℝ) * ε * μ) * α
      + (k : ℝ) * ((k : ℝ) * α * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α
      := by ring
  rw [hgoal]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [abs_le]
  constructor <;> linarith [h22.1, h22.2, h1.1, h1.2, h2.1, h2.2,
    h3.1, h3.2]

/-- **Strict diagonal argmax is stable under small perturbations**
    (Lemma 10.11 stage engine): if the pivot choice has gap `δ` and the
    diagonal perturbation is below `δ/2`, the perturbed matrix selects
    the same pivot. -/
lemma strict_argmax_diag_stable {n : ℕ} (A E : Fin n → Fin n → ℝ)
    (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    ∀ i : Fin n, i ≠ p → A i i + E i i < A p p + E p p := by
  intro i hip
  have h1 := abs_lt.mp (hE i)
  have h2 := abs_lt.mp (hE p)
  have h3 := hgap i hip
  linarith [h1.2, h2.1]

/-- **Deterministic complete-pivoting choice**: the least-index
    maximizer of the diagonal (Lemma 10.11 pivot-sequence
    foundation). -/
noncomputable def diagArgmax {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i)).min'
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)

/-- The deterministic pivot maximizes the diagonal. -/
lemma diagArgmax_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (j : Fin n) : A j j ≤ A (diagArgmax hn A) (diagArgmax hn A) := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i))
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)
  exact (Finset.mem_filter.mp hmem).2 j

/-- A strict maximizer is the deterministic pivot. -/
lemma diagArgmax_eq_of_strict {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hstrict : ∀ i : Fin n, i ≠ p → A i i < A p p) :
    diagArgmax hn A = p := by
  by_contra hne
  have hmax := diagArgmax_max hn A p
  exact absurd hmax (not_le.mpr (hstrict _ hne))

/-- **Pivot-choice stability** (Lemma 10.11, single stage, packaged):
    a gap-`δ` complete-pivoting choice is preserved by any diagonal
    perturbation below `δ/2` — both matrices select the same
    deterministic pivot. -/
theorem diagArgmax_stable {n : ℕ} (hn : 0 < n)
    (A E : Fin n → Fin n → ℝ) (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    diagArgmax hn A = p ∧
    diagArgmax hn (fun i j => A i j + E i j) = p := by
  have hδpos : 0 < δ := by
    have := abs_nonneg (E p p)
    linarith [hE p]
  constructor
  · exact diagArgmax_eq_of_strict hn A p fun i hip => by
      have := hgap i hip
      linarith
  · exact diagArgmax_eq_of_strict hn _ p fun i hip =>
      strict_argmax_diag_stable A E p δ hgap hE i hip

/-- **One complete-pivoting elimination step** (Lemma 10.11 state
    machine): eliminate pivot `p`, zeroing its row and column and
    forming the Schur update on the rest. Dimension is preserved so the
    stage recursion needs no dependent reindexing. -/
noncomputable def schurStep {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else A i j - A i p * A p j / A p p

/-- `schurStep` preserves symmetry. -/
lemma schurStep_symm {n : ℕ} (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i) (i j : Fin n) :
    schurStep A p i j = schurStep A p j i := by
  unfold schurStep
  by_cases hi : i = p
  · by_cases hj : j = p <;> simp [hi, hj]
  · by_cases hj : j = p
    · simp [hi, hj]
    · simp only [hi, hj, or_self, if_false]
      rw [hsym i j, hsym i p, hsym p j]
      ring

/-- **`schurStep` preserves positive semidefiniteness** (the
    completion-of-squares invariant of the Lemma 10.11 stage
    recursion): with a positive pivot, the zeroed Schur update of a PSD
    matrix is PSD — the quadratic form of the update at `x` equals the
    quadratic form of `A` at `x` with the `p`-th coordinate replaced by
    the minimizer `−(∑_{j≠p} a_pj x_j)/a_pp`. -/
lemma schurStep_isPosSemiDef {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (p : Fin n) (hp : 0 < A p p) :
    IsPosSemiDef n (schurStep A p) := by
  refine ⟨schurStep_symm A p hPSD.1, ?_⟩
  intro x
  set d : ℝ := A p p with hd
  set u : ℝ := ∑ j ∈ Finset.univ.erase p, A p j * x j with hu
  set z : Fin n → ℝ := fun i => if i = p then -u / d else x i with hz
  -- the quadratic form of the update, reduced to the erased square
  have hSquad : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrow : ∑ j : Fin n, x p * schurStep A p p j * x j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        unfold schurStep; simp
    rw [hrow, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hip : i ≠ p := Finset.ne_of_mem_erase hi
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hcol : x i * schurStep A p i p * x p = 0 := by
      unfold schurStep; simp
    rw [hcol, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjp : j ≠ p := Finset.ne_of_mem_erase hj
    unfold schurStep
    simp [hip, hjp, ← hd]
  -- the quadratic form of A at the completed vector z
  have hAquad : ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j =
      (-u / d) * d * (-u / d) + (-u / d) * u + u * (-u / d) +
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * A i j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrowp : ∑ j : Fin n, z p * A p j * z j =
        (-u / d) * d * (-u / d) + (-u / d) * u := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
      have hzp : z p = -u / d := by simp [hz]
      have htail : ∑ j ∈ Finset.univ.erase p, z p * A p j * z j =
          (-u / d) * u := by
        rw [hu, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        rw [hzp]
        simp only [hz, hjp, if_false]
        ring
      rw [htail, hzp, hd]
    rw [hrowp]
    have hrest : ∑ i ∈ Finset.univ.erase p,
        ∑ j : Fin n, z i * A i j * z j =
        u * (-u / d) + ∑ i ∈ Finset.univ.erase p,
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
      have hsw : ∀ i ∈ Finset.univ.erase p,
          ∑ j : Fin n, z i * A i j * z j =
          x i * A i p * (-u / d) +
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
        intro i hi
        have hip : i ≠ p := Finset.ne_of_mem_erase hi
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        have hzi : z i = x i := by simp [hz, hip]
        have hzp : z p = -u / d := by simp [hz]
        rw [hzi, hzp]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        simp [hz, hjp]
      rw [Finset.sum_congr rfl hsw, Finset.sum_add_distrib]
      congr 1
      have : ∑ i ∈ Finset.univ.erase p, x i * A i p * (-u / d) =
          (∑ i ∈ Finset.univ.erase p, A p i * x i) * (-u / d) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hPSD.1 i p]
        ring
      rw [this]
    rw [hrest]
    ring
  -- the cross term collapses: quadForm S x = quadForm A z
  have hfactor : ∑ i ∈ Finset.univ.erase p,
      ∑ j ∈ Finset.univ.erase p,
        x i * (A i p * A p j / d) * x j = u * u / d := by
    have hsep : ∀ i ∈ Finset.univ.erase p,
        ∑ j ∈ Finset.univ.erase p,
          x i * (A i p * A p j / d) * x j =
        (A p i * x i / d) * u := by
      intro i hi
      rw [hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hPSD.1 i p]
      ring
    rw [Finset.sum_congr rfl hsep, ← Finset.sum_mul,
      ← Finset.sum_div, ← hu]
    ring
  have hkey : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j := by
    rw [hSquad, hAquad]
    have hsub : ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j =
        (∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
          x i * A i j * x j) - u * u / d := by
      rw [← hfactor, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsub]
    field_simp
    ring
  rw [hkey]
  exact hPSD.2 z

/-- **The complete-pivoting state machine** (Lemma 10.11): stage `t`'s
    working matrix — `A` eliminated `t` times, each time at the
    deterministic diagonal argmax. -/
noncomputable def cpState {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => schurStep (cpState hn A t)
      (diagArgmax hn (cpState hn A t))

/-- The pivot selected at stage `t`. -/
noncomputable def cpPivot {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (cpState hn A t)

/-- Every complete-pivoting stage is symmetric. -/
lemma cpState_symm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i) :
    ∀ t : ℕ, ∀ i j : Fin n, cpState hn A t i j = cpState hn A t j i := by
  intro t
  induction t with
  | zero => exact hsym
  | succ t ih => exact schurStep_symm (cpState hn A t) _ ih

/-- **Every complete-pivoting stage is PSD** while the selected pivots
    stay positive (Lemma 10.11 stage invariant). -/
lemma cpState_isPosSemiDef {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) (t : ℕ)
    (hpiv : ∀ s : ℕ, s < t →
      0 < cpState hn A s (cpPivot hn A s) (cpPivot hn A s)) :
    IsPosSemiDef n (cpState hn A t) := by
  induction t with
  | zero => exact hPSD
  | succ t ih =>
    exact schurStep_isPosSemiDef (cpState hn A t)
      (ih fun s hs => hpiv s (Nat.lt_succ_of_lt hs)) _
      (hpiv t (Nat.lt_succ_self t))

/-- **The selected pivot dominates the whole working diagonal** —
    what complete pivoting means at each stage. -/
lemma cpPivot_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (t : ℕ) (j : Fin n) :
    cpState hn A t j j ≤
      cpState hn A t (cpPivot hn A t) (cpPivot hn A t) :=
  diagArgmax_max hn (cpState hn A t) j

/-- **Entrywise perturbation of one elimination step** (Lemma 10.11
    propagation engine): if `A` and `B` agree entrywise to `ε`, `A` has
    entry cap `c`, and both share the pivot floor `ρ > 0` at `p`, the
    eliminated matrices agree to `ε + (3c²ε + cε²)/ρ²`. Iterating this
    bound across stages propagates a diagonal gap through the
    complete-pivoting recursion. -/
lemma schurStep_entrywise_perturbation {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (p : Fin n) (ε c ρ : ℝ)
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hAB : ∀ i j : Fin n, |A i j - B i j| ≤ ε)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hdA : ρ ≤ A p p) (hdB : ρ ≤ B p p) :
    ∀ i j : Fin n, |schurStep A p i j - schurStep B p i j| ≤
      ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
  intro i j
  have hrhs0 : (0:ℝ) ≤ ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
    positivity
  by_cases hij : i = p ∨ j = p
  · unfold schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold schurStep
    rw [if_neg hij, if_neg hij]
    have hdA0 : (0:ℝ) < A p p := lt_of_lt_of_le hρ hdA
    have hdB0 : (0:ℝ) < B p p := lt_of_lt_of_le hρ hdB
    -- common-denominator form of the update difference
    have hkey : A i p * A p j / A p p - B i p * B p j / B p p =
        (A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)) / (A p p * B p p) := by
      field_simp
      ring
    -- numerator and denominator bounds
    have hBpj : |B p j| ≤ c + ε := by
      have h1 := hAB p j
      have h2 := hcap p j
      have := abs_sub_abs_le_abs_sub (B p j) (A p j)
      rw [abs_sub_comm (B p j) (A p j)] at this
      linarith [this, h1, h2]
    have hnum : |A i p * A p j * (B p p - A p p)
        + A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤
        3 * c ^ 2 * ε + c * ε ^ 2 := by
      have h1 : |A i p * A p j * (B p p - A p p)| ≤ c * c * ε := by
        rw [abs_mul, abs_mul, abs_sub_comm]
        exact mul_le_mul (mul_le_mul (hcap i p) (hcap p j)
          (abs_nonneg _) hc) (hAB p p)
          (abs_nonneg _) (by positivity)
      have h2 : |A i p * (A p j - B p j)| ≤ c * ε := by
        rw [abs_mul]
        exact mul_le_mul (hcap i p) (hAB p j) (abs_nonneg _) hc
      have h3 : |(A i p - B i p) * B p j| ≤ ε * (c + ε) := by
        rw [abs_mul]
        exact mul_le_mul (hAB i p) hBpj (abs_nonneg _) hε
      have h4 : |A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤ c * (c * ε + ε * (c + ε)) := by
        rw [abs_mul]
        refine mul_le_mul (hcap p p) ?_ (abs_nonneg _) hc
        calc |A i p * (A p j - B p j) + (A i p - B i p) * B p j|
            ≤ |A i p * (A p j - B p j)| + |(A i p - B i p) * B p j| :=
              abs_add_le _ _
          _ ≤ c * ε + ε * (c + ε) := add_le_add h2 h3
      calc |A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)|
          ≤ |A i p * A p j * (B p p - A p p)|
            + |A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| := abs_add_le _ _
        _ ≤ c * c * ε + c * (c * ε + ε * (c + ε)) := add_le_add h1 h4
        _ = 3 * c ^ 2 * ε + c * ε ^ 2 := by ring
    have hden : ρ ^ 2 ≤ A p p * B p p := by nlinarith
    have hquot : |A i p * A p j / A p p - B i p * B p j / B p p| ≤
        (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
      rw [hkey, abs_div, abs_of_pos (mul_pos hdA0 hdB0)]
      calc |A i p * A p j * (B p p - A p p)
            + A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| / (A p p * B p p)
          ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / (A p p * B p p) := by
            gcongr
        _ ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
            gcongr

    -- assemble with the direct entry difference
    have hsplit : A i j - A i p * A p j / A p p -
        (B i j - B i p * B p j / B p p) =
        (A i j - B i j) -
        (A i p * A p j / A p p - B i p * B p j / B p p) := by ring
    rw [hsplit]
    have h1 := abs_le.mp (hAB i j)
    have h2 := abs_le.mp hquot
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Lemma 10.11 (no-tie pivot-sequence stability), full stage
    induction**: if every stage `t < r` of the exact complete-pivoting
    recursion on `A` has diagonal gap `δ`, pivot floor `ρ ≥ δ`, and
    entry cap `c`, and the error budget `g` absorbs the one-stage
    growth `ε ↦ ε + (3c²ε + cε²)/(ρ/2)²` while staying below `δ/2`,
    then a perturbed matrix `B` within `ε₀ ≤ g 0` of `A` selects the
    SAME pivot sequence through `r` stages, with stage states
    `g`-close. -/
theorem cpPivot_sequence_stable {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) (r : ℕ)
    (ε₀ δ ρ c : ℝ) (hε₀ : 0 ≤ ε₀) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hc : 0 ≤ c) (g : ℕ → ℝ) (hg0 : ε₀ ≤ g 0)
    (hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤ g (t + 1))
    (hghalf : ∀ t : ℕ, t < r → g t < δ / 2)
    (hAB : ∀ i j : Fin n, |A i j - B i j| ≤ ε₀)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - cpState hn B t i j| ≤ g t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = cpPivot hn B s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  -- the budget is nonnegative along the run
  have hg_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ g t := by
    intro t
    induction t with
    | zero => intro _; linarith
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hgstep t ht'
      have hadd : (0:ℝ) ≤
          (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun i j => (hAB i j).trans hg0,
      fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    -- perturbed stage selects the same pivot
    set Et : Fin n → Fin n → ℝ :=
      fun i j => cpState hn B t i j - cpState hn A t i j with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have h := hdiff i i
      rw [abs_sub_comm] at h
      exact lt_of_le_of_lt h (hghalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hBfun : (fun i j => cpState hn A t i j + Et i j) =
        cpState hn B t := by
      funext i j
      simp [hEt]
    have hpivB : cpPivot hn B t = p := by
      show diagArgmax hn (cpState hn B t) = p
      rw [← hBfun]
      exact hstable.2
    -- one-stage error growth at the shared pivot
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hBfloor : ρ / 2 ≤ cpState hn B t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : cpState hn B t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    have hstep := schurStep_entrywise_perturbation
      (cpState hn A t) (cpState hn B t) p (g t) c (ρ / 2)
      (hg_nonneg t (Nat.le_of_lt ht')) hc (by linarith)
      hdiff (hcap t ht') hAfloor hBfloor
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSB : cpState hn B (t + 1) =
          schurStep (cpState hn B t) p := by
        show schurStep (cpState hn B t) (cpPivot hn B t) =
          schurStep (cpState hn B t) p
        rw [hpivB]
      rw [hSA, hSB]
      exact (hstep i j).trans (hgstep t ht')
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivB]

/-- **Lemma 10.11, source form**: a matrix whose complete-pivoting run
    has no ties (gap `δ`, floor `ρ`, cap `c` through `r` stages) admits
    a positive perturbation radius within which every matrix selects
    the same pivot sequence — the "for sufficiently small `E`"
    statement, instantiating `cpPivot_sequence_stable` with the
    geometric budget `g t = ε₀ K^t`, `K = 1 + (3c² + c)/(ρ/2)²`. -/
theorem cpPivot_sequence_stable_small {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ B : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, |A i j - B i j| ≤ ε₀) →
        ∀ s : ℕ, s < r → cpPivot hn A s = cpPivot hn B s := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hK1 : (1:ℝ) ≤ K := by
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hKr : (0:ℝ) < K ^ r := pow_pos hK0 r
  set ε₀ : ℝ := min 1 (δ / 2) / (2 * K ^ r) with hε₀def
  have hmin0 : (0:ℝ) < min 1 (δ / 2) :=
    lt_min one_pos (by linarith)
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    positivity
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro B hAB
  set g : ℕ → ℝ := fun t => ε₀ * K ^ t with hg
  -- geometric budget stays below both 1 and δ/2 through the run
  have hgle : ∀ t : ℕ, t ≤ r → g t ≤ min 1 (δ / 2) / 2 := by
    intro t htr
    have hpow : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    have : g t = ε₀ * K ^ t := rfl
    rw [this, hε₀def]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
      (by norm_num : (0:ℝ) < 2)]
    calc min 1 (δ / 2) * K ^ t * 2
        ≤ min 1 (δ / 2) * K ^ r * 2 := by
          have := hmin0.le
          nlinarith
      _ = min 1 (δ / 2) * (2 * K ^ r) := by ring
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := by
    intro t htr
    have h := hgle t (Nat.le_of_lt htr)
    have h1 : min 1 (δ / 2) ≤ 1 := min_le_left _ _
    linarith
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := by
    intro t htr
    have h := hgle t (Nat.le_of_lt htr)
    have h1 : min 1 (δ / 2) ≤ δ / 2 := min_le_right _ _
    linarith [hmin0]
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    have : g t = ε₀ * K ^ t := rfl
    rw [this]
    positivity
  -- the geometric budget absorbs the one-stage growth
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    have hstep : g (t + 1) = g t * K := by
      show ε₀ * K ^ (t + 1) = ε₀ * K ^ t * K
      ring
    rw [hstep, hK]
    have hexp : g t * (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) =
        g t + (3 * c ^ 2 * g t + c * g t) / (ρ / 2) ^ 2 := by
      field_simp
    rw [hexp]
    gcongr
    nlinarith
  have hmain := cpPivot_sequence_stable hn A B r ε₀ δ ρ c
    hε₀pos.le hδ hδρ hc g
    (by
      show ε₀ ≤ ε₀ * K ^ 0
      simp)
    hgstep hghalf hAB hgap hfloor hcap
  intro s hs
  exact (hmain r le_rfl).2 s hs

end NumStability

namespace NumStability

/-- **Floating-point elimination step** (Theorem 10.14 pivoted-trace
    route): the fl-arithmetic analogue of `schurStep` — one Schur
    update computed with rounded multiply, divide, and subtract. -/
noncomputable def fl_schurStep (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else fp.fl_sub (A i j) (fp.fl_div (fp.fl_mul (A i p) (A p j)) (A p p))

/-- **One-stage fl-vs-exact proximity**: with entry cap `c` and pivot
    floor `ρ > 0`, the floating-point elimination step is entrywise
    within `u(c + c²/ρ) + (c²/ρ)(2u + u²)(1 + u)` of the exact one —
    the seed of the induction that transfers the exact complete-pivoting
    invariants (pivot sequence via Lemma 10.11, tail domination via
    (10.13)) to the computed factor. -/
theorem fl_schurStep_close (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hfloor : ρ ≤ A p p) :
    ∀ i j : Fin n, |fl_schurStep fp A p i j - schurStep A p i j| ≤
      fp.u * (c + c ^ 2 / ρ) +
        (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
  intro i j
  have hu0 := fp.u_nonneg
  have hrhs0 : (0:ℝ) ≤ fp.u * (c + c ^ 2 / ρ) +
      (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
    positivity
  by_cases hij : i = p ∨ j = p
  · unfold fl_schurStep schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold fl_schurStep schurStep
    rw [if_neg hij, if_neg hij]
    have hd0 : A p p ≠ 0 := (lt_of_lt_of_le hρ hfloor).ne'
    have hdpos : (0:ℝ) < A p p := lt_of_lt_of_le hρ hfloor
    obtain ⟨δ₁, hδ₁, hmul⟩ := fp.model_mul (A i p) (A p j)
    obtain ⟨δ₂, hδ₂, hdiv⟩ := fp.model_div
      (fp.fl_mul (A i p) (A p j)) (A p p) hd0
    obtain ⟨δ₃, hδ₃, hsub⟩ := fp.model_sub (A i j)
      (fp.fl_div (fp.fl_mul (A i p) (A p j)) (A p p))
    rw [hsub, hdiv, hmul]
    -- the quotient magnitude is capped by c²/ρ
    have hquot : |A i p * A p j / A p p| ≤ c ^ 2 / ρ := by
      rw [abs_div, abs_of_pos hdpos]
      have hnum : |A i p * A p j| ≤ c ^ 2 := by
        rw [abs_mul]
        calc |A i p| * |A p j| ≤ c * c :=
              mul_le_mul (hcap i p) (hcap p j) (abs_nonneg _) hc
          _ = c ^ 2 := by ring
      calc |A i p * A p j| / A p p ≤ c ^ 2 / A p p := by gcongr
        _ ≤ c ^ 2 / ρ := by gcongr
    have hS : |A i j - A i p * A p j / A p p| ≤ c + c ^ 2 / ρ := by
      calc |A i j - A i p * A p j / A p p|
          ≤ |A i j| + |A i p * A p j / A p p| := by
            have h := abs_add_le (A i j) (-(A i p * A p j / A p p))
            rw [abs_neg, ← sub_eq_add_neg] at h
            exact h
        _ ≤ c + c ^ 2 / ρ := add_le_add (hcap i j) hquot
    -- algebraic form of the error
    have hexpand : (A i j - A i p * A p j * (1 + δ₁) / A p p * (1 + δ₂))
          * (1 + δ₃) - (A i j - A i p * A p j / A p p) =
        (A i j - A i p * A p j / A p p) * δ₃ -
        A i p * A p j / A p p *
          ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃)) := by
      field_simp
      ring
    rw [hexpand]
    have herr : |(1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃)| ≤
        (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
      have h1 : (1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃) =
          (δ₁ + δ₂ + δ₁ * δ₂) * (1 + δ₃) := by ring
      rw [h1, abs_mul]
      have h2 : |δ₁ + δ₂ + δ₁ * δ₂| ≤ 2 * fp.u + fp.u ^ 2 := by
        have ha := abs_le.mp hδ₁
        have hb := abs_le.mp hδ₂
        have hab : |δ₁ * δ₂| ≤ fp.u ^ 2 := by
          rw [abs_mul]
          calc |δ₁| * |δ₂| ≤ fp.u * fp.u :=
                mul_le_mul hδ₁ hδ₂ (abs_nonneg _) hu0
            _ = fp.u ^ 2 := by ring
        have hab' := abs_le.mp hab
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2,
          hab'.1, hab'.2]
      have h3 : |1 + δ₃| ≤ 1 + fp.u := by
        have := abs_le.mp hδ₃
        rw [abs_le]
        constructor <;> linarith [this.1, this.2, hu0]
      exact mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    calc |(A i j - A i p * A p j / A p p) * δ₃ -
          A i p * A p j / A p p *
            ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))|
        ≤ |(A i j - A i p * A p j / A p p) * δ₃| +
          |A i p * A p j / A p p *
            ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))| := by
          have h := abs_add_le
            ((A i j - A i p * A p j / A p p) * δ₃)
            (-(A i p * A p j / A p p *
              ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))))
          rw [abs_neg, ← sub_eq_add_neg] at h
          exact h
      _ ≤ (c + c ^ 2 / ρ) * fp.u +
          (c ^ 2 / ρ) * ((2 * fp.u + fp.u ^ 2) * (1 + fp.u)) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            exact mul_le_mul hS hδ₃ (abs_nonneg _) (by positivity)
          · rw [abs_mul]
            exact mul_le_mul hquot herr (abs_nonneg _) (by positivity)
      _ = fp.u * (c + c ^ 2 / ρ) +
          (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by ring

/-- **The floating-point complete-pivoting trace**: iterate the fl
    elimination step, choosing each pivot as the argmax of the
    *computed* working diagonal — the algorithm as actually run. -/
noncomputable def fl_cpState (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => fl_schurStep fp (fl_cpState fp hn A t)
      (diagArgmax hn (fl_cpState fp hn A t))

/-- The pivot the floating-point run selects at stage `t`. -/
noncomputable def fl_cpPivot (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (fl_cpState fp hn A t)

/-- **The floating-point run follows the exact pivot sequence**
    (Theorem 10.14 `c`/`η` discharge, stage induction): if the exact
    complete-pivoting trace has gap `δ`, floor `ρ ≥ δ`, cap `c` through
    `r` stages, and the budget `h` starts at `0`, absorbs per stage the
    exact-perturbation growth plus the one-stage rounding contribution
    `U = u(c' + c'²/(ρ/2)) + (c'²/(ρ/2))(2u + u²)(1 + u)` with
    `c' = c + δ/2`, and stays below `δ/2`, then the computed trace
    selects the SAME pivots as exact complete pivoting through `r`
    stages, with working matrices `h`-close throughout. -/
theorem fl_cpPivot_sequence_agrees (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) ≤ h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpState fp hn A t i j| ≤ h t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = fl_cpPivot fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hh_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ h t := by
    intro t
    induction t with
    | zero => intro _; rw [hh0]
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hhstep t ht'
      have h1 : (0:ℝ) ≤
          (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2 : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u) := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i j => ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    show |cpState hn A 0 i j - fl_cpState fp hn A 0 i j| ≤ h 0
    show |A i j - A i j| ≤ h 0
    rw [sub_self, abs_zero, hh0]
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    have hht0 := hh_nonneg t (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    -- the computed stage selects the exact pivot
    set Et : Fin n → Fin n → ℝ :=
      fun i j => fl_cpState fp hn A t i j - cpState hn A t i j
      with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have hd := hdiff i i
      rw [abs_sub_comm] at hd
      exact lt_of_le_of_lt hd (hhhalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hFfun : (fun i j => cpState hn A t i j + Et i j) =
        fl_cpState fp hn A t := by
      funext i j
      simp [hEt]
    have hpivF : fl_cpPivot fp hn A t = p := by
      show diagArgmax hn (fl_cpState fp hn A t) = p
      rw [← hFfun]
      exact hstable.2
    -- caps and floors for the computed working matrix
    have hFcap : ∀ i j : Fin n,
        |fl_cpState fp hn A t i j| ≤ c + δ / 2 := by
      intro i j
      have h1 := hdiff i j
      have h2 := hcap t ht' i j
      have h3 := abs_sub_abs_le_abs_sub
        (fl_cpState fp hn A t i j) (cpState hn A t i j)
      rw [abs_sub_comm (fl_cpState fp hn A t i j)
        (cpState hn A t i j)] at h3
      have h4 := hhhalf t ht'
      linarith
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hFfloor : ρ / 2 ≤ fl_cpState fp hn A t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : fl_cpState fp hn A t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    -- exact-vs-exact perturbation at the shared pivot
    have hexact := schurStep_entrywise_perturbation
      (cpState hn A t) (fl_cpState fp hn A t) p (h t) c (ρ / 2)
      hht0 hc (by linarith) hdiff (hcap t ht') hAfloor hFfloor
    -- fl-vs-exact rounding at the computed working matrix
    have hround := fl_schurStep_close fp (fl_cpState fp hn A t) p
      (c + δ / 2) (ρ / 2) (by linarith) (by linarith)
      hFcap hFfloor
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSF : fl_cpState fp hn A (t + 1) =
          fl_schurStep fp (fl_cpState fp hn A t) p := by
        show fl_schurStep fp (fl_cpState fp hn A t)
          (diagArgmax hn (fl_cpState fp hn A t)) =
          fl_schurStep fp (fl_cpState fp hn A t) p
        rw [show diagArgmax hn (fl_cpState fp hn A t) =
          fl_cpPivot fp hn A t from rfl, hpivF]
      rw [hSA, hSF]
      have htri : |schurStep (cpState hn A t) p i j -
          fl_schurStep fp (fl_cpState fp hn A t) p i j| ≤
          |schurStep (cpState hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j| +
          |fl_schurStep fp (fl_cpState fp hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j| := by
        have habs := abs_add_le
          (schurStep (cpState hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j)
          (schurStep (fl_cpState fp hn A t) p i j -
            fl_schurStep fp (fl_cpState fp hn A t) p i j)
        rw [sub_add_sub_cancel] at habs
        rw [abs_sub_comm (fl_schurStep fp (fl_cpState fp hn A t) p i j)
          (schurStep (fl_cpState fp hn A t) p i j)]
        exact habs
      calc |schurStep (cpState hn A t) p i j -
            fl_schurStep fp (fl_cpState fp hn A t) p i j|
          ≤ _ + _ := htri
        _ ≤ (h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2) +
            (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
                (1 + fp.u)) :=
            add_le_add (hexact i j) (hround i j)
        _ ≤ h (t + 1) := by
            have := hhstep t ht'
            linarith
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivF]

/-- **The computed stopping test certifies the exact trailing Schur
    complement** (displays (10.23)/(10.24) for the algorithm as run):
    under the pivot-agreement hypotheses, if the computed working
    diagonal at stage `r` passes the termination test
    `max_i S̃_ii ≤ tol`, then EVERY entry of the exact stage-`r` Schur
    complement is at most `tol + h r` in absolute value — the
    `η`-reading for the Theorem 10.14 certificate: exact trailing
    smallness from a computed test plus the accumulated budget. -/
theorem fl_cp_termination_trailing_bound (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) ≤ h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (tol : ℝ)
    (hterm : ∀ i : Fin n, fl_cpState fp hn A r i i ≤ tol) :
    ∀ i j : Fin n, |cpState hn A r i j| ≤ tol + h r := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  -- the exact stage-r state is PSD
  have hSr : IsPosSemiDef n (cpState hn A r) :=
    cpState_isPosSemiDef hn A hPSD r fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s hs)
  -- the computed and exact stage-r states are h r-close
  have hagree := fl_cpPivot_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    h hh0 hhstep hhhalf hgap hfloor hcap r le_rfl
  have hdiff := hagree.1
  -- exact trailing diagonal from the computed test
  have hdiag : ∀ i : Fin n, cpState hn A r i i ≤ tol + h r := by
    intro i
    have h1 := hdiff i i
    have h2 := abs_le.mp h1
    have h3 := hterm i
    linarith [h2.2]
  exact psd_abs_entry_le_maxdiag (cpState hn A r) hSr (tol + h r)
    hdiag
/-- **Factor-form floating-point elimination step** — the update as
    Algorithm 10.2-pivoted actually computes it: divide the pivot row
    and column by the rounded square root of the pivot and subtract
    the product of the computed factor entries. -/
noncomputable def fl_schurStepFactor (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else fp.fl_sub (A i j)
      (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))

/-- **Factor-form one-stage proximity**: the √-scaled fl update is
    entrywise within `u(c + c²/ρ) + (1+u)γ₅(c²/ρ)` of the exact Schur
    step — five rounding factors (one shared square root entering
    twice reciprocally, two divides, one multiply) against the sharp
    Stewart-counter bound `γ₅`, plus the final subtraction. -/
theorem fl_schurStepFactor_close (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hfloor : ρ ≤ A p p) (h5 : gammaValid fp 5) :
    ∀ i j : Fin n,
      |fl_schurStepFactor fp A p i j - schurStep A p i j| ≤
      fp.u * (c + c ^ 2 / ρ) +
        (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by
  intro i j
  have hu0 := fp.u_nonneg
  have hu1 : fp.u < 1 := by
    unfold gammaValid at h5
    push_cast at h5
    nlinarith
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  have hrhs0 : (0:ℝ) ≤ fp.u * (c + c ^ 2 / ρ) +
      (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by positivity
  by_cases hij : i = p ∨ j = p
  · unfold fl_schurStepFactor schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold fl_schurStepFactor schurStep
    rw [if_neg hij, if_neg hij]
    have hdpos : (0:ℝ) < A p p := lt_of_lt_of_le hρ hfloor
    have hsq : (0:ℝ) < Real.sqrt (A p p) := Real.sqrt_pos.mpr hdpos
    obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (A p p) hdpos.le
    have h1a : (0:ℝ) < 1 + δa := by
      have := abs_le.mp hδa
      linarith [this.1]
    have hfs0 : fp.fl_sqrt (A p p) ≠ 0 := by
      rw [hsqrt]
      positivity
    obtain ⟨δb, hδb, hdivb⟩ := fp.model_div (A i p)
      (fp.fl_sqrt (A p p)) hfs0
    obtain ⟨δc, hδc, hdivc⟩ := fp.model_div (A p j)
      (fp.fl_sqrt (A p p)) hfs0
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul
      (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
      (fp.fl_div (A p j) (fp.fl_sqrt (A p p)))
    obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A i j)
      (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))
    set C : ℝ := (1 + δb) * (1 + δc) * (1 + δm) /
      ((1 + δa) * (1 + δa)) with hC
    -- the computed product is the exact quotient times the counter C
    have hprod : fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))) =
        A i p * A p j / A p p * C := by
      rw [hmul, hdivb, hdivc, hsqrt, hC]
      field_simp
      rw [Real.sq_sqrt hdpos.le]
      ring
    -- C is a five-factor Stewart counter
    have hcounter : relErrorCounter fp 5 C := by
      refine ⟨![δb, δc, δm, δa, δa],
        ![false, false, false, true, true], ?_, ?_⟩
      · intro i
        fin_cases i <;> simpa
      · rw [hC, Fin.prod_univ_five]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        field_simp
    have hC1 : |C - 1| ≤ gamma fp 5 :=
      relErrorCounter_abs_sub_one_le_gamma fp 5 C hcounter h5
    -- quotient magnitude and exact-entry magnitude
    have hquot : |A i p * A p j / A p p| ≤ c ^ 2 / ρ := by
      rw [abs_div, abs_of_pos hdpos]
      have hnum : |A i p * A p j| ≤ c ^ 2 := by
        rw [abs_mul]
        calc |A i p| * |A p j| ≤ c * c :=
              mul_le_mul (hcap i p) (hcap p j) (abs_nonneg _) hc
          _ = c ^ 2 := by ring
      calc |A i p * A p j| / A p p ≤ c ^ 2 / A p p := by gcongr
        _ ≤ c ^ 2 / ρ := by gcongr
    have hS : |A i j - A i p * A p j / A p p| ≤ c + c ^ 2 / ρ := by
      have h := abs_add_le (A i j) (-(A i p * A p j / A p p))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h.trans (add_le_add (hcap i j) hquot)
    -- expand the computed entry
    rw [hsub, hprod]
    have hexpand : (A i j - A i p * A p j / A p p * C) * (1 + δs) -
        (A i j - A i p * A p j / A p p) =
        (A i j - A i p * A p j / A p p) * δs -
        A i p * A p j / A p p * ((C - 1) * (1 + δs)) := by ring
    rw [hexpand]
    have h1s : |1 + δs| ≤ 1 + fp.u := by
      have := abs_le.mp hδs
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    calc |(A i j - A i p * A p j / A p p) * δs -
          A i p * A p j / A p p * ((C - 1) * (1 + δs))|
        ≤ |(A i j - A i p * A p j / A p p) * δs| +
          |A i p * A p j / A p p * ((C - 1) * (1 + δs))| := by
          have h := abs_add_le
            ((A i j - A i p * A p j / A p p) * δs)
            (-(A i p * A p j / A p p * ((C - 1) * (1 + δs))))
          rw [abs_neg, ← sub_eq_add_neg] at h
          exact h
      _ ≤ (c + c ^ 2 / ρ) * fp.u +
          (c ^ 2 / ρ) * (gamma fp 5 * (1 + fp.u)) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            exact mul_le_mul hS hδs (abs_nonneg _) (by positivity)
          · rw [abs_mul, abs_mul]
            refine mul_le_mul hquot ?_
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (by positivity)
            exact mul_le_mul hC1 h1s (abs_nonneg _) hγ5
      _ = fp.u * (c + c ^ 2 / ρ) +
          (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by ring

/-- **The factor-form floating-point complete-pivoting trace**: the
    pivoted algorithm as actually implemented — √-scaled fl updates,
    pivots from the computed working diagonal. -/
noncomputable def fl_cpStateFactor (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => fl_schurStepFactor fp (fl_cpStateFactor fp hn A t)
      (diagArgmax hn (fl_cpStateFactor fp hn A t))

/-- The pivot the factor-form run selects at stage `t`. -/
noncomputable def fl_cpPivotFactor (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (fl_cpStateFactor fp hn A t)

/-- **The factor-form run follows the exact pivot sequence** — the
    `fl_cpPivot_sequence_agrees` induction for the √-scaled
    formulation, with the `γ₅` Stewart rounding contribution
    `U = u(c′ + c′²/(ρ/2)) + (1+u)γ₅(c′²/(ρ/2))`, `c′ = c + δ/2`. -/
theorem fl_cpPivotFactor_sequence_agrees (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤ h t) ∧
      (∀ s : ℕ, s < t →
        cpPivot hn A s = fl_cpPivotFactor fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  have hh_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ h t := by
    intro t
    induction t with
    | zero => intro _; rw [hh0]
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hhstep t ht'
      have h1 : (0:ℝ) ≤
          (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2 : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i j => ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    show |A i j - A i j| ≤ h 0
    rw [sub_self, abs_zero, hh0]
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    have hht0 := hh_nonneg t (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    set Et : Fin n → Fin n → ℝ :=
      fun i j => fl_cpStateFactor fp hn A t i j - cpState hn A t i j
      with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have hd := hdiff i i
      rw [abs_sub_comm] at hd
      exact lt_of_le_of_lt hd (hhhalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hFfun : (fun i j => cpState hn A t i j + Et i j) =
        fl_cpStateFactor fp hn A t := by
      funext i j
      simp [hEt]
    have hpivF : fl_cpPivotFactor fp hn A t = p := by
      show diagArgmax hn (fl_cpStateFactor fp hn A t) = p
      rw [← hFfun]
      exact hstable.2
    have hFcap : ∀ i j : Fin n,
        |fl_cpStateFactor fp hn A t i j| ≤ c + δ / 2 := by
      intro i j
      have h1 := hdiff i j
      have h2 := hcap t ht' i j
      have h3 := abs_sub_abs_le_abs_sub
        (fl_cpStateFactor fp hn A t i j) (cpState hn A t i j)
      rw [abs_sub_comm (fl_cpStateFactor fp hn A t i j)
        (cpState hn A t i j)] at h3
      have h4 := hhhalf t ht'
      linarith
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hFfloor : ρ / 2 ≤ fl_cpStateFactor fp hn A t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : fl_cpStateFactor fp hn A t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    have hexact := schurStep_entrywise_perturbation
      (cpState hn A t) (fl_cpStateFactor fp hn A t) p (h t) c (ρ / 2)
      hht0 hc (by linarith) hdiff (hcap t ht') hAfloor hFfloor
    have hround := fl_schurStepFactor_close fp
      (fl_cpStateFactor fp hn A t) p (c + δ / 2) (ρ / 2)
      (by linarith) (by linarith) hFcap hFfloor h5
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSF : fl_cpStateFactor fp hn A (t + 1) =
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p := by
        show fl_schurStepFactor fp (fl_cpStateFactor fp hn A t)
          (diagArgmax hn (fl_cpStateFactor fp hn A t)) =
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p
        rw [show diagArgmax hn (fl_cpStateFactor fp hn A t) =
          fl_cpPivotFactor fp hn A t from rfl, hpivF]
      rw [hSA, hSF]
      have htri : |schurStep (cpState hn A t) p i j -
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j| ≤
          |schurStep (cpState hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j| +
          |fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j| := by
        have habs := abs_add_le
          (schurStep (cpState hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j)
          (schurStep (fl_cpStateFactor fp hn A t) p i j -
            fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j)
        rw [sub_add_sub_cancel] at habs
        rw [abs_sub_comm
          (fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j)
          (schurStep (fl_cpStateFactor fp hn A t) p i j)]
        exact habs
      calc |schurStep (cpState hn A t) p i j -
            fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j|
          ≤ _ + _ := htri
        _ ≤ (h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2) +
            (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              (1 + fp.u) * gamma fp 5 *
                ((c + δ / 2) ^ 2 / (ρ / 2))) :=
            add_le_add (hexact i j) (hround i j)
        _ ≤ h (t + 1) := by
            have := hhstep t ht'
            linarith
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivF]

/-- **Computed factor rows are pivot-dominated** (the `c`-discharge for
    Theorem 10.14's domination hypothesis, one stage): if the exact
    working matrix is PSD with maximal pivot and floor `ρ`, and the
    computed working matrix is `ht`-close (`ht ≤ ρ/4`), then every
    computed off-pivot factor entry `fl(S̃_pj / √S̃_pp)` is bounded by
    `(1 + 4ht/ρ)(1+u)/(1−u)²` times the computed pivot entry
    `fl(√S̃_pp)` — the computed form of the (10.13) invariant, with the
    domination constant explicit. -/
theorem fl_factor_row_dominated (fp : FPModel) {n : ℕ}
    (S Stilde : Fin n → Fin n → ℝ) (p : Fin n) (ρ ht : ℝ)
    (hPSD : IsPosSemiDef n S)
    (hmax : ∀ j : Fin n, S j j ≤ S p p)
    (hfloorS : ρ ≤ S p p) (hρ : 0 < ρ)
    (hht : 0 ≤ ht) (hht2 : ht ≤ ρ / 4)
    (hclose : ∀ i j : Fin n, |S i j - Stilde i j| ≤ ht)
    (hu1 : fp.u < 1) :
    ∀ j : Fin n,
      |fp.fl_div (Stilde p j) (fp.fl_sqrt (Stilde p p))| ≤
      (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (Stilde p p)| := by
  intro j
  have hu0 := fp.u_nonneg
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  -- the computed pivot is well above zero
  have hSpp : ρ ≤ S p p := hfloorS
  have hStpp : ρ / 2 ≤ Stilde p p := by
    have h1 := abs_le.mp (hclose p p)
    linarith [h1.2]
  have hStpp0 : (0:ℝ) < Stilde p p := by linarith
  have hsq0 : (0:ℝ) < Real.sqrt (Stilde p p) :=
    Real.sqrt_pos.mpr hStpp0
  obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (Stilde p p) hStpp0.le
  have ha := abs_le.mp hδa
  have h1a : (0:ℝ) < 1 + δa := by linarith [ha.1]
  have hfs0 : fp.fl_sqrt (Stilde p p) ≠ 0 := by
    rw [hsqrt]; positivity
  obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (Stilde p j)
    (fp.fl_sqrt (Stilde p p)) hfs0
  have hb := abs_le.mp hδb
  -- numerator control through the exact PSD structure
  have hnum : |Stilde p j| ≤ Stilde p p * (1 + 4 * ht / ρ) := by
    have h1 : |Stilde p j| ≤ |S p j| + ht := by
      have h := hclose p j
      have h2 := abs_sub_abs_le_abs_sub (Stilde p j) (S p j)
      rw [abs_sub_comm (Stilde p j) (S p j)] at h2
      linarith
    have h2 : |S p j| ≤ S p p := by
      calc |S p j| ≤ Real.sqrt (S p p) * Real.sqrt (S j j) :=
            psd_abs_entry_le_sqrt_diag S hPSD p j
        _ ≤ Real.sqrt (S p p) * Real.sqrt (S p p) :=
            mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hmax j)) (Real.sqrt_nonneg _)
        _ = S p p := Real.mul_self_sqrt (by linarith)
    have h3 : S p p ≤ Stilde p p + ht := by
      have h := abs_le.mp (hclose p p)
      linarith [h.1]
    have h4 : Stilde p p + 2 * ht ≤
        Stilde p p * (1 + 4 * ht / ρ) := by
      rw [mul_add, mul_one]
      have : Stilde p p * (4 * ht / ρ) ≥ 2 * ht := by
        rw [ge_iff_le, show Stilde p p * (4 * ht / ρ) =
          Stilde p p * 4 * ht / ρ by ring, le_div_iff₀ hρ]
        nlinarith
      linarith
    linarith
  -- assemble through the model factors
  rw [hdiv, hsqrt]
  rw [abs_mul, abs_div, abs_mul, abs_of_pos hsq0, abs_of_pos h1a]
  have h1b : |1 + δb| ≤ 1 + fp.u := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  have hda : (1:ℝ) - fp.u ≤ 1 + δa := by linarith [ha.1]
  have hsqSt : Real.sqrt (Stilde p p) * Real.sqrt (Stilde p p) =
      Stilde p p := Real.mul_self_sqrt hStpp0.le
  -- |S̃ p j| / (√·(1+δa)) · |1+δb| ≤ target
  calc |Stilde p j| / (Real.sqrt (Stilde p p) * (1 + δa)) *
        |1 + δb|
      ≤ (Stilde p p * (1 + 4 * ht / ρ)) /
          (Real.sqrt (Stilde p p) * (1 - fp.u)) * (1 + fp.u) := by
        refine mul_le_mul ?_ h1b (abs_nonneg _) (by positivity)
        refine div_le_div₀ (by positivity) hnum (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)
    _ = (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 - fp.u)) := by
        field_simp
        nlinarith [hsqSt]
    _ ≤ (1 + 4 * ht / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
          (Real.sqrt (Stilde p p) * (1 + δa)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)) ?_
        positivity

/-- **All computed factor rows are pivot-dominated across the run**
    (Theorem 10.14 `c`-discharge, composed): under the no-tie data and
    the rounding budget (bounded by `ρ/4`), at every stage `t < r` of
    the factor-form floating-point run, every computed off-pivot factor
    entry is at most `(1 + 4·h t/ρ)(1+u)/(1−u)²` times the computed
    pivot entry — the computed (10.13) invariant for the whole run,
    with per-stage explicit constants. -/
theorem fl_cpFactor_rows_dominated (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t < r → ∀ j : Fin n,
      |fp.fl_div (fl_cpStateFactor fp hn A t (cpPivot hn A t) j)
        (fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t)))| ≤
      (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
        |fp.fl_sqrt (fl_cpStateFactor fp hn A t
          (cpPivot hn A t) (cpPivot hn A t))| := by
  intro t htr j
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu1 : fp.u < 1 := by
    unfold gammaValid at h5
    push_cast at h5
    nlinarith [fp.u_nonneg]
  -- stage data from the agreement induction and the exact invariants
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap t
    (Nat.le_of_lt htr)
  have hclose := hagree.1
  have hSPSD : IsPosSemiDef n (cpState hn A t) :=
    cpState_isPosSemiDef hn A hPSD t fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
  have hht0 : 0 ≤ h t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hh0]
    · have h1 := hhhalf t htr
      -- nonnegativity via the budget recurrence from stage t-1
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0.ne'
      have ht'r : t' < r := lt_trans (Nat.lt_succ_self t') htr
      have hstep := hhstep t' ht'r
      have haux : ∀ s : ℕ, s ≤ t' → 0 ≤ h s := by
        intro s
        induction s with
        | zero => intro _; rw [hh0]
        | succ s ihs =>
          intro hsr
          have hs' : s < r := by omega
          have h0 := ihs (by omega)
          have hst := hhstep s hs'
          have h1' : (0:ℝ) ≤
              (3 * c ^ 2 * h s + c * h s ^ 2) / (ρ / 2) ^ 2 := by
            positivity
          have h2' : (0:ℝ) ≤
              fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              (1 + fp.u) * gamma fp 5 *
                ((c + δ / 2) ^ 2 / (ρ / 2)) := by
            have hγ := gamma_nonneg fp h5
            have hu0 := fp.u_nonneg
            refine add_nonneg (by positivity)
              (mul_nonneg (mul_nonneg (by positivity) hγ)
                (by positivity))
          linarith
      have h0 := haux t' le_rfl
      have h1' : (0:ℝ) ≤
          (3 * c ^ 2 * h t' + c * h t' ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2' : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) := by
        have hγ := gamma_nonneg fp h5
        have hu0 := fp.u_nonneg
        refine add_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (by positivity) hγ)
            (by positivity))
      linarith
  exact fl_factor_row_dominated fp (cpState hn A t)
    (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
    hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
    (hht4 t htr) hclose hu1 j

/-- The exact scaled pivot row extracted at one elimination stage:
    `√(a_pp)` at the pivot, `a_pj/√(a_pp)` elsewhere. -/
noncomputable def schurRow {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) : Fin n → ℝ :=
  fun i => if i = p then Real.sqrt (A p p)
    else A p i / Real.sqrt (A p p)

/-- **One elimination step subtracts the scaled pivot-row outer
    product** — entrywise, at every position including the zeroed
    pivot row and column. -/
lemma schurStep_decompose {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) (hsym : ∀ i j : Fin n, A i j = A j i)
    (hp : 0 < A p p) :
    ∀ i j : Fin n, schurStep A p i j =
      A i j - schurRow A p i * schurRow A p j := by
  intro i j
  have hsq : Real.sqrt (A p p) * Real.sqrt (A p p) = A p p :=
    Real.mul_self_sqrt hp.le
  have hsq0 : Real.sqrt (A p p) ≠ 0 :=
    (Real.sqrt_pos.mpr hp).ne'
  unfold schurStep schurRow
  by_cases hi : i = p
  · by_cases hj : j = p
    · rw [hi, hj, if_pos (Or.inl rfl), if_pos rfl, hsq]
      ring
    · rw [hi, if_pos (Or.inl rfl), if_pos rfl, if_neg hj,
        show Real.sqrt (A p p) * (A p j / Real.sqrt (A p p)) =
          A p j * (Real.sqrt (A p p) / Real.sqrt (A p p)) by ring,
        div_self hsq0]
      ring
  · by_cases hj : j = p
    · rw [hj, if_pos (Or.inr rfl), if_neg hi, if_pos rfl,
        show A p i / Real.sqrt (A p p) * Real.sqrt (A p p) =
          A p i * (Real.sqrt (A p p) / Real.sqrt (A p p)) by ring,
        div_self hsq0, hsym p i]
      ring
    · rw [if_neg (by simp [hi, hj]), if_neg hi, if_neg hj,
        show A p i / Real.sqrt (A p p) *
          (A p j / Real.sqrt (A p p)) =
          A p i * A p j / (Real.sqrt (A p p) * Real.sqrt (A p p))
          by ring, hsq, hsym p i]

/-- **The exact run telescopes**: after `r` stages,
    `A = ∑_{t<r} row_tᵀ row_t + S_r` entrywise — the Gram assembly of
    the exact pivoted factorization, with `S_r` the stage-`r` Schur
    complement (Theorem 10.14 / (10.22) exact skeleton). -/
theorem cpState_telescope {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hsym : ∀ i j : Fin n, A i j = A j i)
    (r : ℕ)
    (hfloor : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t)) :
    ∀ i j : Fin n,
      A i j = (∑ t ∈ Finset.range r,
        schurRow (cpState hn A t) (cpPivot hn A t) i *
        schurRow (cpState hn A t) (cpPivot hn A t) j) +
        cpState hn A r i j := by
  induction r with
  | zero =>
    intro i j
    simp [cpState]
  | succ r ih =>
    intro i j
    have hfloor' : ∀ t : ℕ, t < r →
        0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t) :=
      fun t ht => hfloor t (Nat.lt_succ_of_lt ht)
    have hsymr : ∀ i j : Fin n,
        cpState hn A r i j = cpState hn A r j i :=
      cpState_symm hn A hsym r
    have hstep := schurStep_decompose (cpState hn A r)
      (cpPivot hn A r) hsymr (hfloor r (Nat.lt_succ_self r)) i j
    have hS : cpState hn A (r + 1) i j =
        cpState hn A r i j -
        schurRow (cpState hn A r) (cpPivot hn A r) i *
        schurRow (cpState hn A r) (cpPivot hn A r) j := hstep
    have hih := ih hfloor' i j
    rw [Finset.sum_range_succ, hS]
    linarith [hih]

/-- **The fl pivot-agreement hypotheses are non-vacuous** (instantiated
    budget): with `U` the one-stage rounding contribution and
    `K = 1 + (3c² + c)/(ρ/2)²` the exact-growth rate, the explicit
    budget `g t = U·t·Kᵗ` satisfies the recurrence, so a single scalar
    smallness condition `U·r·Kʳ < min(min 1 (δ/2)) (ρ/4)` — which holds
    for all sufficiently small `u`, since `U` is a polynomial in `u`
    vanishing at `0` — yields pivot agreement and state closeness
    outright. -/
theorem fl_cpPivot_sequence_agrees_small (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall :
      (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
        ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
          (1 + fp.u)) * r *
        (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpState fp hn A t i j| ≤
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) * t *
          (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = fl_cpPivot fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  set U : ℝ := fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
    ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
      (1 + fp.u) with hU
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hK1 : (1:ℝ) ≤ K := by
    rw [hK]
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  set g : ℕ → ℝ := fun t => U * t * K ^ t with hg
  -- the budget is capped along the run by the smallness scalar
  have hgle : ∀ t : ℕ, t ≤ r →
      g t ≤ U * r * K ^ r := by
    intro t htr
    show U * t * K ^ t ≤ U * r * K ^ r
    have h1 : (t:ℝ) ≤ (r:ℝ) := by exact_mod_cast htr
    have h2 : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    calc U * t * K ^ t ≤ U * r * K ^ t := by
          have := mul_le_mul_of_nonneg_left h1 hU0
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ U * r * K ^ r := by
          exact mul_le_mul_of_nonneg_left h2
            (mul_nonneg hU0 (Nat.cast_nonneg r))
  have hM := hsmall
  have hmin1 : min (min 1 (δ / 2)) (ρ / 4) ≤ 1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hminδ : min (min 1 (δ / 2)) (ρ / 4) ≤ δ / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  -- the explicit budget satisfies all three conditions
  have hg0 : g 0 = 0 := by
    show U * (0:ℕ) * K ^ 0 = 0
    norm_num
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := fun t htr =>
    le_trans (hgle t (Nat.le_of_lt htr)) (le_of_lt
      (lt_of_lt_of_le hM hmin1))
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := fun t htr =>
    lt_of_le_of_lt (hgle t (Nat.le_of_lt htr))
      (lt_of_lt_of_le hM hminδ)
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    show (0:ℝ) ≤ U * t * K ^ t
    positivity
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    -- quadratic absorbed at g ≤ 1, then the K-recurrence
    have habs : 3 * c ^ 2 * g t + c * g t ^ 2 ≤
        (3 * c ^ 2 + c) * g t := by
      nlinarith [mul_nonneg (mul_nonneg hc hgt0)
        (sub_nonneg.mpr hgt1)]
    have hKrec : g t * K + U ≤ g (t + 1) := by
      show U * t * K ^ t * K + U ≤ U * ((t + 1 : ℕ) : ℝ) * K ^ (t + 1)
      push_cast
      have h1 : (1:ℝ) ≤ K ^ (t + 1) := one_le_pow₀ hK1
      have h2 : U * (t:ℝ) * K ^ t * K = U * (t:ℝ) * K ^ (t + 1) := by
        rw [pow_succ]; ring
      nlinarith [h2, mul_nonneg hU0 (sub_nonneg.mpr h1)]
    have hexp : g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 =
        g t * K := by
      rw [hK]
      field_simp
    have hdiv : (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 := by gcongr
    calc g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U
        ≤ g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 + U := by
          linarith [hdiv]
      _ = g t * K + U := by rw [hexp]
      _ ≤ g (t + 1) := hKrec
  exact fl_cpPivot_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    g hg0 hgstep hghalf hgap hfloor hcap

/-- **Factor-form fl agreement, non-vacuous form**: the explicit budget
    `g t = U·t·Kᵗ` with the `γ₅` rounding contribution — one scalar
    smallness condition, holding for all sufficiently small `u`. -/
theorem fl_cpPivotFactor_sequence_agrees_small (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall :
      (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
        (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) * r *
        (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) * t *
          (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ t) ∧
      (∀ s : ℕ, s < t →
        cpPivot hn A s = fl_cpPivotFactor fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  set U : ℝ := fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
    (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) with hU
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hU0 : 0 ≤ U := by
    rw [hU]
    refine add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by positivity) hγ5) (by positivity))
  have hK1 : (1:ℝ) ≤ K := by
    rw [hK]
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  set g : ℕ → ℝ := fun t => U * t * K ^ t with hg
  have hgle : ∀ t : ℕ, t ≤ r → g t ≤ U * r * K ^ r := by
    intro t htr
    show U * t * K ^ t ≤ U * r * K ^ r
    have h1 : (t:ℝ) ≤ (r:ℝ) := by exact_mod_cast htr
    have h2 : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    calc U * t * K ^ t ≤ U * r * K ^ t := by
          have := mul_le_mul_of_nonneg_left h1 hU0
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ U * r * K ^ r :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg hU0 (Nat.cast_nonneg r))
  have hmin1 : min (min 1 (δ / 2)) (ρ / 4) ≤ 1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hminδ : min (min 1 (δ / 2)) (ρ / 4) ≤ δ / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hg0 : g 0 = 0 := by
    show U * (0:ℕ) * K ^ 0 = 0
    norm_num
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := fun t htr =>
    le_trans (hgle t (Nat.le_of_lt htr))
      (le_of_lt (lt_of_lt_of_le hsmall hmin1))
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := fun t htr =>
    lt_of_le_of_lt (hgle t (Nat.le_of_lt htr))
      (lt_of_lt_of_le hsmall hminδ)
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    show (0:ℝ) ≤ U * t * K ^ t
    positivity
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    have habs : 3 * c ^ 2 * g t + c * g t ^ 2 ≤
        (3 * c ^ 2 + c) * g t := by
      nlinarith [mul_nonneg (mul_nonneg hc hgt0)
        (sub_nonneg.mpr hgt1)]
    have hKrec : g t * K + U ≤ g (t + 1) := by
      show U * t * K ^ t * K + U ≤ U * ((t + 1 : ℕ) : ℝ) * K ^ (t + 1)
      push_cast
      have h1 : (1:ℝ) ≤ K ^ (t + 1) := one_le_pow₀ hK1
      have h2 : U * (t:ℝ) * K ^ t * K = U * (t:ℝ) * K ^ (t + 1) := by
        rw [pow_succ]; ring
      nlinarith [h2, mul_nonneg hU0 (sub_nonneg.mpr h1)]
    have hexp : g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 =
        g t * K := by
      rw [hK]
      field_simp
    have hdiv : (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 := by gcongr
    calc g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U
        ≤ g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 + U := by
          linarith [hdiv]
      _ = g t * K + U := by rw [hexp]
      _ ≤ g (t + 1) := hKrec
  exact fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    h5 g hg0 hgstep hghalf hgap hfloor hcap

/-- **Neumann-style entry cap for the perturbed inverse** (resolves the
    recorded Lemma 10.10 `χ`-as-hypothesis delta): from the resolvent
    identity alone, if `q = k²με < 1` then every entry of `X` is
    bounded by `μ/(1−q)` — no cap on `X` needs to be assumed. Proof by
    evaluating the identity at the maximal entry. -/
lemma resolvent_entry_cap {k : ℕ} (hk : 0 < k)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ) (μ ε : ℝ)
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) (hE : ∀ i j, |E11 i j| ≤ ε)
    (hX : X = M - M * E11 * X)
    (hq : (k:ℝ) ^ 2 * μ * ε < 1) :
    ∀ i j, |X i j| ≤ μ / (1 - (k:ℝ) ^ 2 * μ * ε) := by
  have hne : (Finset.univ : Finset (Fin k × Fin k)).Nonempty := by
    refine ⟨(⟨0, hk⟩, ⟨0, hk⟩), Finset.mem_univ _⟩
  set χ : ℝ := Finset.univ.sup' hne
    (fun p : Fin k × Fin k => |X p.1 p.2|) with hχ
  have hbound : ∀ i j : Fin k, |X i j| ≤ χ := fun i j =>
    Finset.le_sup' (f := fun p : Fin k × Fin k => |X p.1 p.2|)
      (Finset.mem_univ (i, j))
  have hχ0 : 0 ≤ χ := le_trans (abs_nonneg _)
    (hbound ⟨0, hk⟩ ⟨0, hk⟩)
  -- the sup is attained
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne
    (fun p : Fin k × Fin k => |X p.1 p.2|)
  -- entrywise bound on the correction term at any entry
  have hME : ∀ (i t : Fin k), |(M * E11) i t| ≤ (k:ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE
  have hMEX : ∀ (i j : Fin k), |((M * E11) * X) i j| ≤
      (k:ℝ) * ((k:ℝ) * μ * ε) * χ :=
    entrywise_matMul_le (M * E11) X _ χ (by positivity) hME hbound
  -- evaluate the identity at the attaining entry
  have hself : χ ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ := by
    have hXe : X p.1 p.2 = M p.1 p.2 - ((M * E11) * X) p.1 p.2 := by
      conv_lhs => rw [hX]
      simp [Matrix.sub_apply]
    have h1 : |X p.1 p.2| ≤ |M p.1 p.2| + |((M * E11) * X) p.1 p.2| := by
      rw [hXe]
      have h := abs_add_le (M p.1 p.2) (-(((M * E11) * X) p.1 p.2))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have h2 := hMEX p.1 p.2
    have h3 : (k:ℝ) * ((k:ℝ) * μ * ε) * χ =
        (k:ℝ) ^ 2 * μ * ε * χ := by ring
    have hpχ : χ = |X p.1 p.2| := by
      rw [hχ]; exact hp
    have hcalc : |X p.1 p.2| ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ :=
      calc |X p.1 p.2|
          ≤ |M p.1 p.2| + |((M * E11) * X) p.1 p.2| := h1
        _ ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ := by
            rw [← h3]
            exact add_le_add (hM p.1 p.2) h2
    linarith [hpχ, hcalc]
  have h1q : (0:ℝ) < 1 - (k:ℝ) ^ 2 * μ * ε := by linarith
  have hχle : χ ≤ μ / (1 - (k:ℝ) ^ 2 * μ * ε) := by
    rw [le_div_iff₀ h1q]
    nlinarith
  exact fun i j => le_trans (hbound i j) hχle

/-- The computed factor row extracted at one fl elimination stage:
    `fl(√a_pp)` at the pivot, `fl(a_pj/fl(√a_pp))` off it. -/
noncomputable def fl_cpRowOf (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → ℝ :=
  fun j => if j = p then fp.fl_sqrt (A p p)
    else fp.fl_div (A p j) (fp.fl_sqrt (A p p))

/-- **Per-stage defect of the fl factorization step** (R̂-Gram bridge
    engine): the fl update differs from
    `A − (computed row)ᵀ(computed row)` entrywise by at most
    `u|a_ij| + (2u+u²)|r̃_i||r̃_j|`. On the pivot row and column the
    computed square root cancels *exactly* as a real number, so only
    the divide's single rounding survives; on the diagonal the
    `(1+δ)²` of the square root is absorbed for `u ≤ 1/8`. -/
theorem fl_schurStepFactor_defect_bound (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hApp : 0 < A p p) (hu8 : fp.u ≤ 1 / 8) :
    ∀ i j : Fin n,
      |fl_schurStepFactor fp A p i j -
        (A i j - fl_cpRowOf fp A p i * fl_cpRowOf fp A p j)| ≤
      fp.u * |A i j| + (2 * fp.u + fp.u ^ 2) *
        (|fl_cpRowOf fp A p i| * |fl_cpRowOf fp A p j|) := by
  intro i j
  have hu0 := fp.u_nonneg
  obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (A p p) hApp.le
  have ha := abs_le.mp hδa
  have h1a : (0:ℝ) < 1 + δa := by nlinarith [ha.1]
  have hsq0 : (0:ℝ) < Real.sqrt (A p p) := Real.sqrt_pos.mpr hApp
  have hfs0 : fp.fl_sqrt (A p p) ≠ 0 := by
    rw [hsqrt]; positivity
  have hsqsq : Real.sqrt (A p p) * Real.sqrt (A p p) = A p p :=
    Real.mul_self_sqrt hApp.le
  by_cases hi : i = p
  · -- pivot row: exact real cancellation of the square root
    obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (A p j)
      (fp.fl_sqrt (A p p)) hfs0
    by_cases hj : j = p
    · -- diagonal: (1+δa)² absorbed at u ≤ 1/8
      unfold fl_schurStepFactor fl_cpRowOf
      rw [hi, hj, if_pos (Or.inl rfl), if_pos rfl, hsqrt]
      have hkey : (0:ℝ) - (A p p - Real.sqrt (A p p) * (1 + δa) *
          (Real.sqrt (A p p) * (1 + δa))) =
          A p p * ((1 + δa) * (1 + δa) - 1) := by
        nlinarith [hsqsq]
      rw [hkey, abs_mul, abs_of_pos hApp]
      have herr : |(1 + δa) * (1 + δa) - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
        have h1 : (1 + δa) * (1 + δa) - 1 = 2 * δa + δa ^ 2 := by ring
        rw [h1]
        have h2 : |δa ^ 2| ≤ fp.u ^ 2 := by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hδa 2
        have h3 := abs_le.mp h2
        rw [abs_le]
        constructor <;> nlinarith [ha.1, ha.2, h3.1, h3.2]
      have hrow2 : |Real.sqrt (A p p) * (1 + δa)| *
          |Real.sqrt (A p p) * (1 + δa)| =
          A p p * ((1 + δa) * (1 + δa)) := by
        rw [abs_mul, abs_of_pos hsq0, abs_of_pos h1a]
        nlinarith [hsqsq]
      calc A p p * |(1 + δa) * (1 + δa) - 1|
          ≤ A p p * (2 * fp.u + fp.u ^ 2) :=
            mul_le_mul_of_nonneg_left herr hApp.le
        _ ≤ fp.u * A p p + (2 * fp.u + fp.u ^ 2) *
              (A p p * ((1 + δa) * (1 + δa))) := by
            have hge : (1 - fp.u) * (1 - fp.u) ≤
                (1 + δa) * (1 + δa) := by
              nlinarith [ha.1, hu8, hu0]
            have h5 : A p p * ((2 * fp.u + fp.u ^ 2) *
                ((1 - fp.u) * (1 - fp.u))) ≤
                A p p * ((2 * fp.u + fp.u ^ 2) *
                ((1 + δa) * (1 + δa))) := by
              refine mul_le_mul_of_nonneg_left ?_ hApp.le
              exact mul_le_mul_of_nonneg_left hge (by positivity)
            have hcoef : 2 * fp.u + fp.u ^ 2 ≤ fp.u +
                (2 * fp.u + fp.u ^ 2) *
                  ((1 - fp.u) * (1 - fp.u)) := by
              nlinarith [mul_nonneg hu0
                (by linarith : (0:ℝ) ≤ 1 - 4 * fp.u),
                pow_nonneg hu0 4, sq_nonneg fp.u]
            nlinarith [h5, mul_le_mul_of_nonneg_left hcoef hApp.le]
        _ = fp.u * A p p + (2 * fp.u + fp.u ^ 2) *
              (|Real.sqrt (A p p) * (1 + δa)| *
               |Real.sqrt (A p p) * (1 + δa)|) := by
            rw [hrow2]
    · unfold fl_schurStepFactor fl_cpRowOf
      rw [hi, if_pos (Or.inl rfl), if_pos rfl, if_neg hj, hdiv, hsqrt]
      have hcancel : (0:ℝ) - (A p j - Real.sqrt (A p p) * (1 + δa) *
          (A p j / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb))) =
          A p j * δb := by
        field_simp
        ring
      rw [hcancel, abs_mul]
      have h1 : |A p j| * |δb| ≤ fp.u * |A p j| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hδb (abs_nonneg _)
      have h2 : (0:ℝ) ≤ (2 * fp.u + fp.u ^ 2) *
          (|Real.sqrt (A p p) * (1 + δa)| *
           |A p j / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb)|) := by
        positivity
      linarith
  · by_cases hj : j = p
    · -- pivot column: same exact cancellation, via symmetry
      obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (A p i)
        (fp.fl_sqrt (A p p)) hfs0
      unfold fl_schurStepFactor fl_cpRowOf
      rw [hj, if_pos (Or.inr rfl), if_neg hi, if_pos rfl, hdiv, hsqrt]
      have hcancel : (0:ℝ) - (A i p -
          A p i / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb) *
            (Real.sqrt (A p p) * (1 + δa))) =
          A i p * δb := by
        rw [hsym p i]
        field_simp
        ring
      rw [hcancel, abs_mul]
      have h1 : |A i p| * |δb| ≤ fp.u * |A i p| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hδb (abs_nonneg _)
      have h2 : (0:ℝ) ≤ (2 * fp.u + fp.u ^ 2) *
          (|A p i / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb)| *
           |Real.sqrt (A p p) * (1 + δa)|) := by
        positivity
      linarith
    · -- off-pivot: the multiply and subtract roundings
      obtain ⟨δb, hδb, hdivb⟩ := fp.model_div (A i p)
        (fp.fl_sqrt (A p p)) hfs0
      obtain ⟨δc, hδc, hdivc⟩ := fp.model_div (A p j)
        (fp.fl_sqrt (A p p)) hfs0
      obtain ⟨δm, hδm, hmul⟩ := fp.model_mul
        (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p)))
      obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A i j)
        (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
          (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))
      unfold fl_schurStepFactor fl_cpRowOf
      rw [if_neg (by simp [hi, hj]), if_neg hi, if_neg hj,
        hsub, hmul, hdivb, hdivc]
      have hrow_i : fp.fl_div (A p i) (fp.fl_sqrt (A p p)) =
          A i p / fp.fl_sqrt (A p p) * (1 + δb) := by
        rw [hsym p i]
        exact hdivb
      rw [hrow_i]
      have hexp : (A i j - A i p / fp.fl_sqrt (A p p) * (1 + δb) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc)) * (1 + δm)) *
            (1 + δs) -
          (A i j - A i p / fp.fl_sqrt (A p p) * (1 + δb) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc))) =
          A i j * δs -
          (A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
            ((1 + δm) * (1 + δs) - 1) := by
        ring
      rw [hexp]
      have herr : |(1 + δm) * (1 + δs) - 1| ≤
          2 * fp.u + fp.u ^ 2 := by
        have h1 : (1 + δm) * (1 + δs) - 1 =
            δm + δs + δm * δs := by ring
        rw [h1]
        have hab : |δm * δs| ≤ fp.u ^ 2 := by
          rw [abs_mul]
          calc |δm| * |δs| ≤ fp.u * fp.u :=
                mul_le_mul hδm hδs (abs_nonneg _) hu0
            _ = fp.u ^ 2 := by ring
        have h2 := abs_le.mp hab
        have h3 := abs_le.mp hδm
        have h4 := abs_le.mp hδs
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
      calc |A i j * δs -
            (A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
              (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
              ((1 + δm) * (1 + δs) - 1)|
          ≤ |A i j * δs| +
            |(A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
              (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
              ((1 + δm) * (1 + δs) - 1)| := by
            have h := abs_add_le (A i j * δs)
              (-((A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
                (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
                ((1 + δm) * (1 + δs) - 1)))
            rw [abs_neg, ← sub_eq_add_neg] at h
            exact h
        _ ≤ fp.u * |A i j| + (2 * fp.u + fp.u ^ 2) *
              (|A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
               |A p j / fp.fl_sqrt (A p p) * (1 + δc)|) := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right hδs (abs_nonneg _)
            · rw [abs_mul, abs_mul]
              rw [show |A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
                  |A p j / fp.fl_sqrt (A p p) * (1 + δc)| *
                  |(1 + δm) * (1 + δs) - 1| =
                  |(1 + δm) * (1 + δs) - 1| *
                  (|A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
                   |A p j / fp.fl_sqrt (A p p) * (1 + δc)|) by ring]
              exact mul_le_mul_of_nonneg_right herr
                (by positivity)

/-- The fl elimination step preserves symmetry, given commutative
    rounded multiplication (true for IEEE; the abstract model does not
    assert it, so it is carried as a hypothesis). -/
lemma fl_schurStepFactor_symm (fp : FPModel)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i) (i j : Fin n) :
    fl_schurStepFactor fp A p i j = fl_schurStepFactor fp A p j i := by
  unfold fl_schurStepFactor
  by_cases hi : i = p
  · by_cases hj : j = p <;> simp [hi, hj]
  · by_cases hj : j = p
    · simp [hi, hj]
    · rw [if_neg (by simp [hi, hj]), if_neg (by simp [hi, hj])]
      rw [hsym i j, hsym i p, hsym p j]
      rw [hmul (fp.fl_div (A p i) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A j p) (fp.fl_sqrt (A p p)))]

/-- The fl trace stays symmetric from a symmetric input. -/
lemma fl_cpStateFactor_symm (fp : FPModel)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i) :
    ∀ t : ℕ, ∀ i j : Fin n,
      fl_cpStateFactor fp hn A t i j = fl_cpStateFactor fp hn A t j i := by
  intro t
  induction t with
  | zero => exact hsym
  | succ t ih =>
    exact fl_schurStepFactor_symm fp hmul
      (fl_cpStateFactor fp hn A t) _ ih

/-- **The as-run factorization telescopes with summable defects**
    (Theorem 10.14 componentwise backward error for the pivoted
    algorithm as actually executed): the Gram of the computed rows,
    plus the terminal computed Schur state, reproduces `A` entrywise up
    to `r` per-stage rounding defects —
    `|∑_{t<r} r̃ᵗᵢ r̃ᵗⱼ + S̃ᵣ ᵢⱼ − aᵢⱼ| ≤ r(u·cS + (2u+u²)·cR²)`. -/
theorem fl_cpFactor_gram_backward_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hsymA : ∀ i j : Fin n, A i j = A j i)
    (hu8 : fp.u ≤ 1 / 8)
    (hpos : ∀ t : ℕ, t < r →
      0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t))
    (cS cR : ℝ)
    (hcapS : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |fl_cpStateFactor fp hn A t i j| ≤ cS)
    (hcapR : ∀ t : ℕ, t < r → ∀ i : Fin n,
      |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) i| ≤ cR) :
    ∀ i j : Fin n,
      |(∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpStateFactor fp hn A r i j - A i j| ≤
      (r : ℝ) * (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) := by
  induction r with
  | zero =>
    intro i j
    simp [fl_cpStateFactor]
  | succ r ih =>
    intro i j
    have hpos' : ∀ t : ℕ, t < r →
        0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
          (fl_cpPivotFactor fp hn A t) :=
      fun t ht => hpos t (Nat.lt_succ_of_lt ht)
    have hcapS' : ∀ t : ℕ, t < r → ∀ i j : Fin n,
        |fl_cpStateFactor fp hn A t i j| ≤ cS :=
      fun t ht => hcapS t (Nat.lt_succ_of_lt ht)
    have hcapR' : ∀ t : ℕ, t < r → ∀ i : Fin n,
        |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
          (fl_cpPivotFactor fp hn A t) i| ≤ cR :=
      fun t ht => hcapR t (Nat.lt_succ_of_lt ht)
    have hih := ih hpos' hcapS' hcapR' i j
    -- the stage-r defect
    have hsymr := fl_cpStateFactor_symm fp hmul hn A hsymA r
    have hdef := fl_schurStepFactor_defect_bound fp
      (fl_cpStateFactor fp hn A r) (fl_cpPivotFactor fp hn A r)
      hsymr (hpos r (Nat.lt_succ_self r)) hu8 i j
    have hSsucc : fl_cpStateFactor fp hn A (r + 1) i j =
        fl_schurStepFactor fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) i j := rfl
    -- bound the stage-r defect by the uniform constant
    have hdef' : |fl_cpStateFactor fp hn A (r + 1) i j -
        (fl_cpStateFactor fp hn A r i j -
          fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
            (fl_cpPivotFactor fp hn A r) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
            (fl_cpPivotFactor fp hn A r) j)| ≤
        fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2 := by
      rw [hSsucc]
      refine hdef.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left
          (hcapS r (Nat.lt_succ_self r) i j) fp.u_nonneg
      · have h1 := hcapR r (Nat.lt_succ_self r) i
        have h2 := hcapR r (Nat.lt_succ_self r) j
        have hcR0 : (0:ℝ) ≤ cR := le_trans (abs_nonneg _) h1
        have : |fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) i| *
            |fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) j| ≤ cR ^ 2 := by
          calc _ ≤ cR * cR :=
                mul_le_mul h1 h2 (abs_nonneg _) hcR0
            _ = cR ^ 2 := by ring
        refine mul_le_mul_of_nonneg_left this ?_
        have := fp.u_nonneg
        positivity
    -- assemble
    rw [Finset.sum_range_succ]
    have hgoal : (∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) i *
        fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) j +
        fl_cpStateFactor fp hn A (r + 1) i j - A i j =
        ((∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
          fl_cpStateFactor fp hn A r i j - A i j) +
        (fl_cpStateFactor fp hn A (r + 1) i j -
          (fl_cpStateFactor fp hn A r i j -
            fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) i *
            fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) j)) := by
      ring
    rw [hgoal]
    calc |_ + _|
        ≤ _ + _ := abs_add_le _ _
      _ ≤ (r : ℝ) * (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) +
          (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) :=
          add_le_add hih hdef'
      _ = ((r + 1 : ℕ) : ℝ) *
          (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) := by
          push_cast
          ring

/-- **Theorem 10.14 for the algorithm as run, fully composed**: under
    the exact trace's no-tie data, the rounding budget (capped at
    `ρ/4`), `u ≤ 1/8`, commutative rounded multiplication, and `A` PSD
    symmetric, the computed pivoted factorization satisfies the
    componentwise backward-error bound
    `|∑_{t<r} r̃ᵗᵢr̃ᵗⱼ + S̃ᵣᵢⱼ − aᵢⱼ| ≤ r(u·cS + (2u+u²)·cR²)` with the
    explicit caps `cS = c + δ/2` and
    `cR = 2(1+u)²/(1−u)²·√(c + δ/2)` discharged from the agreement
    machinery — no cap hypotheses remain. -/
theorem higham10_14_as_run_backward_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hht4 : ∀ t : ℕ, t < r → h t ≤ ρ / 4)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ i j : Fin n,
      |(∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpStateFactor fp hn A r i j - A i j| ≤
      (r : ℝ) * (fp.u * (c + δ / 2) + (2 * fp.u + fp.u ^ 2) *
        (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
          Real.sqrt (c + δ / 2)) ^ 2) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hu1 : fp.u < 1 := by linarith
  have h1u : (0:ℝ) < 1 - fp.u := by linarith
  have hcδ : (0:ℝ) ≤ c + δ / 2 := by linarith
  -- stage data shared by all discharges
  have hagree := fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c
    hδ hδρ hc h5 h hh0 hhstep hhhalf hgap hfloor hcap
  have hstage : ∀ t : ℕ, t < r →
      fl_cpPivotFactor fp hn A t = cpPivot hn A t := by
    intro t htr
    exact ((hagree (t + 1) (Nat.succ_le_of_lt htr)).2 t
      (Nat.lt_succ_self t)).symm
  have hclose : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤ h t :=
    fun t htr => (hagree t (Nat.le_of_lt htr)).1
  have hSfloor : ∀ t : ℕ, t < r → ρ / 2 ≤
      fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t) := by
    intro t htr
    have h1 := abs_le.mp (hclose t htr (cpPivot hn A t)
      (cpPivot hn A t))
    have h2 := hfloor t htr
    have h3 := hhhalf t htr
    linarith [h1.1, hδρ]
  -- pivot positivity for the fl states
  have hpos : ∀ t : ℕ, t < r →
      0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) := by
    intro t htr
    rw [hstage t htr]
    linarith [hSfloor t htr]
  -- state cap
  have hcapS : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |fl_cpStateFactor fp hn A t i j| ≤ c + δ / 2 := by
    intro t htr i j
    have h1 := hclose t htr i j
    have h2 := hcap t htr i j
    have h3 := abs_sub_abs_le_abs_sub
      (fl_cpStateFactor fp hn A t i j) (cpState hn A t i j)
    rw [abs_sub_comm (fl_cpStateFactor fp hn A t i j)
      (cpState hn A t i j)] at h3
    have h4 := hhhalf t htr
    linarith
  -- row cap: pivot entry via the sqrt model, off-pivot via domination
  have hcapR : ∀ t : ℕ, t < r → ∀ i : Fin n,
      |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) i| ≤
      2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
        Real.sqrt (c + δ / 2) := by
    intro t htr i
    have hp := hstage t htr
    have hSp := hSfloor t htr
    have hSpos : (0:ℝ) < fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t) := by linarith
    -- the computed pivot entry
    obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt
      (fl_cpStateFactor fp hn A t (cpPivot hn A t) (cpPivot hn A t))
      hSpos.le
    have ha := abs_le.mp hδa
    have hsqle : Real.sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t)) ≤
        Real.sqrt (c + δ / 2) := by
      apply Real.sqrt_le_sqrt
      have := hcapS t htr (cpPivot hn A t) (cpPivot hn A t)
      calc fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)
          ≤ |fl_cpStateFactor fp hn A t (cpPivot hn A t)
            (cpPivot hn A t)| := le_abs_self _
        _ ≤ c + δ / 2 := this
    have hpivot_cap : |fp.fl_sqrt (fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))| ≤
        (1 + fp.u) * Real.sqrt (c + δ / 2) := by
      rw [hsqrt, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1a : |1 + δa| ≤ 1 + fp.u := by
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2]
      calc Real.sqrt _ * |1 + δa|
          ≤ Real.sqrt (c + δ / 2) * (1 + fp.u) :=
            mul_le_mul hsqle h1a (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = (1 + fp.u) * Real.sqrt (c + δ / 2) := mul_comm _ _
    -- exact-state invariants at stage t for the domination lemma
    have hSPSD : IsPosSemiDef n (cpState hn A t) :=
      cpState_isPosSemiDef hn A hPSD t fun s hs =>
        lt_of_lt_of_le hρ0 (hfloor s (lt_trans hs htr))
    have hht0 : 0 ≤ h t := by
      have h1 := abs_nonneg (cpState hn A t (cpPivot hn A t)
        (cpPivot hn A t) - fl_cpStateFactor fp hn A t
        (cpPivot hn A t) (cpPivot hn A t))
      exact le_trans h1 (hclose t htr _ _)
    have hdom := fl_factor_row_dominated fp (cpState hn A t)
      (fl_cpStateFactor fp hn A t) (cpPivot hn A t) ρ (h t)
      hSPSD (cpPivot_max hn A t) (hfloor t htr) hρ0 hht0
      (hht4 t htr) (hclose t htr) hu1 i
    have hconst : (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) ≤
        2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
      have h1 : 4 * h t / ρ ≤ 1 := by
        rw [div_le_one hρ0]
        linarith [hht4 t htr]
      have h2 : (0:ℝ) ≤ (1 + fp.u) / (1 - fp.u) ^ 2 := by positivity
      have h1' : 1 + 4 * h t / ρ ≤ 2 := by linarith
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2)
          ≤ 2 * ((1 + fp.u) / (1 - fp.u) ^ 2) :=
            mul_le_mul_of_nonneg_right h1' h2
        _ = 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by ring
    unfold fl_cpRowOf
    rw [hp]
    by_cases hip : i = cpPivot hn A t
    · rw [if_pos hip]
      refine hpivot_cap.trans ?_
      have hge1 : (1:ℝ) ≤ 2 * (1 + fp.u) / (1 - fp.u) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (1 + fp.u) * Real.sqrt (c + δ / 2)
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + fp.u)
              (Real.sqrt_nonneg (c + δ / 2)), hge1]
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
    · rw [if_neg hip]
      refine (hdom).trans ?_
      calc (1 + 4 * h t / ρ) * ((1 + fp.u) / (1 - fp.u) ^ 2) *
            |fp.fl_sqrt (fl_cpStateFactor fp hn A t
              (cpPivot hn A t) (cpPivot hn A t))|
          ≤ (2 * (1 + fp.u) / (1 - fp.u) ^ 2) *
            ((1 + fp.u) * Real.sqrt (c + δ / 2)) := by
            refine mul_le_mul hconst hpivot_cap (abs_nonneg _) ?_
            positivity
        _ = 2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
            Real.sqrt (c + δ / 2) := by ring
  exact fl_cpFactor_gram_backward_error fp hn A r hmul hPSD.1 hu8
    hpos (c + δ / 2)
    (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 * Real.sqrt (c + δ / 2))
    hcapS hcapR

-- ============================================================
-- §10.3  Lemma 10.12: W-norm bound
-- ============================================================

/-- **Abstract W-norm bound interface** (Higham §10.3, Lemma 10.12). -/
theorem w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (_hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  hW

/-- **Abstract back-substitution growth** (Lemma 10.13 engine): if each
    `|w i|` is bounded by `1` plus the sum of the later `|w j|` — the
    pivot-normalized form of the triangular solve under the (10.13)
    bounds — then `|w i| ≤ 2^{r-1-i}`, by downward induction with the
    geometric sum `1 + (2^t − 1) = 2^t`. -/
lemma backsub_growth {r : ℕ} (w : Fin r → ℝ)
    (hrec : ∀ i : Fin r, |w i| ≤ 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val), |w j|) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  have H : ∀ (t : ℕ) (i : Fin r), r - 1 - i.val = t →
      |w i| ≤ 2 ^ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IH =>
      intro i hit
      have himg : (Finset.univ.filter
          (fun j : Fin r => i.val < j.val)).image
          (fun j : Fin r => r - 1 - j.val) = Finset.range t := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_range]
        constructor
        · rintro ⟨j, hj, rfl⟩
          have := j.isLt
          omega
        · intro hk
          refine ⟨⟨r - 1 - k, by omega⟩, by simp; omega, by simp; omega⟩
      have hinj : ∀ a ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          ∀ b ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          r - 1 - a.val = r - 1 - b.val → a = b := by
        intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have := a.isLt
        have := b.isLt
        exact Fin.ext (by omega)
      have hsum_exp : ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), (2:ℝ) ^ (r - 1 - j.val) =
          ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by
        rw [← himg, Finset.sum_image hinj]
      calc |w i| ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val), |w j| := hrec i
        _ ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val),
            (2:ℝ) ^ (r - 1 - j.val) := by
            gcongr with j hj
            simp only [Finset.mem_filter, Finset.mem_univ,
              true_and] at hj
            exact IH (r - 1 - j.val) (by have := j.isLt; omega) j rfl
        _ = 1 + ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by rw [hsum_exp]
        _ = 2 ^ t := by
            rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) t]
            ring
  intro i
  exact H (r - 1 - i.val) i rfl

/-- **Entry domination from the column-tail invariant** (Lemma 10.13
    wiring): under the (10.13) invariant, every entry on or right of the
    diagonal is dominated in absolute value by its row pivot. -/
lemma tail_invariant_entry_le {n : ℕ} {R : Fin n → Fin n → ℝ}
    (hdiag_nonneg : ∀ i : Fin n, 0 ≤ R i i)
    (htail : ∀ k j : Fin n, k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2) ≤ R k k ^ 2)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |R k j| ≤ R k k := by
  have hmem : k ∈ Finset.univ.filter
      (fun i : Fin n => k.val ≤ i.val) := by
    simp
  have hsingle : R k j ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (R i j)) hmem
  have hsq : R k j ^ 2 ≤ R k k ^ 2 :=
    le_trans hsingle (htail k j hkj)
  nlinarith [abs_nonneg (R k j), sq_abs (R k j), hdiag_nonneg k]

/-- **Normalized triangular-solve growth** (Lemma 10.13 core): a solve
    `Uw = b` against an upper-triangular matrix whose every row is
    pivot-dominated (`|U i j| ≤ U i i`, `|b i| ≤ U i i` — supplied by the
    (10.13) invariant through `tail_invariant_entry_le`) has solution
    entries bounded by `2^{r-1-i}`. -/
theorem normalized_solve_growth {r : ℕ} (U : Fin r → Fin r → ℝ)
    (b w : Fin r → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hb : ∀ i : Fin r, |b i| ≤ U i i)
    (hsolve : ∀ i : Fin r, ∑ j : Fin r, U i j * w j = b i) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  apply backsub_growth
  intro i
  have hpos := hdiag_pos i
  -- split the solve row at the diagonal: below-diagonal entries vanish
  have hle_part : ∑ j ∈ Finset.univ.filter
      (fun j : Fin r => ¬ i.val < j.val), U i j * w j =
      U i i * w i := by
    refine Finset.sum_eq_single_of_mem i (by simp) ?_
    intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_lt] at hj
    have hjlt : j.val < i.val := by
      rcases Nat.lt_or_eq_of_le hj with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') hji
    rw [hupper i j hjlt, zero_mul]
  have hsplit : U i i * w i +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i j * w j = b i := by
    have h := hsolve i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin r => i.val < j.val) (fun j => U i j * w j),
      hle_part] at h
    linarith [h]
  -- bound the absolute tail sum by pivot-scaled solution magnitudes
  have hsum_abs : |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i i * |w j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum ?_)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hentry i j hj.le) (abs_nonneg _)
  -- triangle inequality on the rearranged pivot equation
  have htri : |U i i * w i| ≤ |b i| + |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| := by
    have heq : U i i * w i = b i - ∑ j ∈ Finset.univ.filter
        (fun j : Fin r => i.val < j.val), U i j * w j := by
      linarith [hsplit]
    rw [heq]
    have h1 := abs_add_le (b i) (-(∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j))
    rw [abs_neg, ← sub_eq_add_neg] at h1
    exact h1
  -- assemble and divide by the positive pivot
  have hwi : U i i * |w i| ≤ U i i * (1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        |w j|) := by
    have habs : U i i * |w i| = |U i i * w i| := by
      rw [abs_mul, abs_of_pos hpos]
    rw [habs, mul_add, mul_one, Finset.mul_sum]
    calc |U i i * w i|
        ≤ |b i| + |∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i j * w j| := htri
      _ ≤ U i i + ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i i * |w j| :=
          add_le_add (hb i) hsum_abs
  exact le_of_mul_le_mul_left hwi hpos

-- ============================================================
-- §10.3  Lemma 10.13: Complete pivoting bound
-- ============================================================

/-- **Squared-sum of the growth bounds**: entries bounded by `2^{r-1-i}`
    have squared sum at most `(4^r − 1)/3` (geometric sum, Higham
    §10.3, proof of Lemma 10.13). -/
lemma sq_sum_pow_two_bound {r : ℕ} (w : Fin r → ℝ)
    (h : ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val)) :
    ∑ i : Fin r, w i ^ 2 ≤ ((4 : ℝ) ^ r - 1) / 3 := by
  have hterm : ∀ i : Fin r, w i ^ 2 ≤ (4 : ℝ) ^ (r - 1 - i.val) := by
    intro i
    obtain ⟨hlo, hhi⟩ := abs_le.mp (h i)
    have hsq : w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 :=
      sq_le_sq' hlo hhi
    calc w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 := hsq
      _ = ((2 : ℝ) ^ 2) ^ (r - 1 - i.val) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ (r - 1 - i.val) := by norm_num
  have hrev : ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) =
      ∑ i : Fin r, (4 : ℝ) ^ i.val := by
    apply Fintype.sum_bijective (Fin.rev) (Fin.rev_involutive.bijective)
    intro i
    rw [Fin.val_rev]
    congr 1
    omega
  have hgeom : ∑ i : Fin r, (4 : ℝ) ^ i.val = ((4 : ℝ) ^ r - 1) / 3 := by
    rw [Fin.sum_univ_eq_sum_range (fun t => (4 : ℝ) ^ t) r,
      geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) r,
      show (4 : ℝ) - 1 = 3 by norm_num]
  calc ∑ i : Fin r, w i ^ 2
      ≤ ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((4 : ℝ) ^ r - 1) / 3 := by rw [hrev, hgeom]

/-- **Complete-pivoting bound on ‖W‖_F²** (Higham §10.3, Lemma 10.13,
    display (10.19)): if the `r × r` upper-triangular block `U` has
    positive diagonal and every row pivot-dominated on and right of the
    diagonal (as `tail_invariant_entry_le` extracts from the (10.13)
    column-tail invariant of complete pivoting), and `W` solves
    `U W = B` column-by-column with `|B i j| ≤ U i i`, then
    `‖W‖_F² ≤ m (4^r − 1)/3` — Higham's `(n − r)(4^r − 1)/3` with
    `m = n − r` border columns. -/
theorem complete_pivoting_w_bound {r m : ℕ} (U : Fin r → Fin r → ℝ)
    (B W : Fin r → Fin m → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hB : ∀ (i : Fin r) (j : Fin m), |B i j| ≤ U i i)
    (hsolve : ∀ (i : Fin r) (j : Fin m),
      ∑ k : Fin r, U i k * W k j = B i j) :
    ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hcol : ∀ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      ((4 : ℝ) ^ r - 1) / 3 := fun j =>
    sq_sum_pow_two_bound (fun i => W i j)
      (normalized_solve_growth U (fun i => B i j) (fun i => W i j)
        hupper hdiag_pos hentry (fun i => hB i j) (fun i => hsolve i j))
  calc ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2
      ≤ ∑ _j : Fin m, ((4 : ℝ) ^ r - 1) / 3 :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

-- ============================================================
-- §10.3  Theorem 10.14: PSD Cholesky error analysis
-- ============================================================

/-- **Abstract backward-error interface for PSD Cholesky**
    (Higham §10.3, Theorem 10.14).

    The hypothesis `hbackward` supplies the detailed pivoted PSD Cholesky
    analysis; this theorem projects the product equation and componentwise
    error bound used by downstream modules. -/
theorem psd_cholesky_backward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (r : ℕ) (_hr : r ≤ n) (_hr_pos : 0 < r)
    (_hPSD : IsPosSemiDef n A)
    (_hn_r : gammaValid fp (r + 1))
    (_hγ_lt : gamma fp (r + 1) < 1)
    (W_norm : ℝ) (_hW : 0 ≤ W_norm)
    (hbackward : ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, j.val < i.val → R_hat i j = 0) ∧
      (∀ i j : Fin n, r ≤ i.val → R_hat i j = 0) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0))) :
    ∃ (R_hat : Fin n → Fin n → ℝ) (E : Fin n → Fin n → ℝ),
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + E i j) ∧
      (∀ i j, |E i j| ≤ gamma fp (r + 1) / (1 - gamma fp (r + 1)) *
        (1 + W_norm) ^ 2 *
        ∑ k : Fin n, |A i k| * (if k.val < r then 1 else 0)) := by
  obtain ⟨R_hat, E, _, _, hprod, hbound⟩ := hbackward
  exact ⟨R_hat, E, hprod, hbound⟩

-- ============================================================
-- §10.3  Termination criteria
-- ============================================================

/-- **Abstract termination-criterion interface (10.27)** for PSD Cholesky. -/
theorem psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (_hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  hstop

end NumStability
