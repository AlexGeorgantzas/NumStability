import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems Cholesky PositiveSemidefinite Basic

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyPSD` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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

end NumStability
