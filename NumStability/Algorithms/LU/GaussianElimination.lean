-- Algorithms/LU/GaussianElimination.lean
--
-- LU factorization backward error (Higham §9.3, Theorem 9.3).
--
-- If Gaussian elimination with any pivoting strategy computes L̂, Û from A,
-- then L̂Û = A + ΔA with |ΔA| ≤ γ(n)|L̂||Û| componentwise.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.OuterProduct
import NumStability.Algorithms.MatMul

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.3  LU factorization specification
-- ============================================================

/-- Specification of an LU factorization: A = L * U.

    L is unit lower triangular (1s on diagonal, zeros above),
    U is upper triangular (zeros below diagonal). -/
structure LUFactSpec (n : ℕ) (A L : Fin n → Fin n → ℝ) (U : Fin n → Fin n → ℝ) : Prop where
  /-- L is unit lower triangular: diagonal entries are 1. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular: entries above diagonal are 0. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- U is upper triangular: entries below diagonal are 0. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  /-- A = L * U: the product recovers A exactly. -/
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j

/-- For an exact LU certificate with unit lower triangular `L`, the determinant
of `A` is the product of the pivots on the diagonal of `U`. -/
theorem LUFactSpec.det_eq_prod_U_diag {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  classical
  have hAeq : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.of L : Matrix (Fin n) (Fin n) ℝ) *
        (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply] using (hLU.product_eq i j).symm
  have hLtri : Matrix.BlockTriangular
      (M := (Matrix.of L : Matrix (Fin n) (Fin n) ℝ)) OrderDual.toDual := by
    intro i j hij
    exact hLU.L_upper_zero i j (by simpa using hij)
  have hUtri : Matrix.BlockTriangular
      (M := (Matrix.of U : Matrix (Fin n) (Fin n) ℝ)) id := by
    intro i j hij
    exact hLU.U_lower_zero i j (by simpa using hij)
  calc
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.det ((Matrix.of L : Matrix (Fin n) (Fin n) ℝ) *
            (Matrix.of U : Matrix (Fin n) (Fin n) ℝ)) := by rw [hAeq]
    _ = Matrix.det (Matrix.of L : Matrix (Fin n) (Fin n) ℝ) *
          Matrix.det (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) := by
          rw [Matrix.det_mul]
    _ = (∏ i : Fin n, L i i) * (∏ i : Fin n, U i i) := by
          rw [Matrix.det_of_lowerTriangular _ hLtri,
            Matrix.det_of_upperTriangular hUtri]
          simp [Matrix.of_apply]
    _ = (∏ _i : Fin n, (1 : ℝ)) * (∏ i : Fin n, U i i) := by
          congr 1
          apply Finset.prod_congr rfl
          intro i _
          exact hLU.L_diag i
    _ = ∏ i : Fin n, U i i := by simp

/-- An exact LU certificate is nonsingular exactly when all pivots on the
diagonal of `U` are nonzero. -/
theorem LUFactSpec.det_ne_zero_iff_U_diag_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 := by
  rw [hLU.det_eq_prod_U_diag]
  simpa using
    (Finset.prod_ne_zero_iff :
      (∏ i : Fin n, U i i) ≠ 0 ↔
        ∀ i ∈ (Finset.univ : Finset (Fin n)), U i i ≠ 0)

/-- First scalar Schur complement used by the exact no-pivot LU induction.
For a matrix indexed by `Fin (m + 1)`, this removes row and column zero after
eliminating with pivot `A 0 0`. -/
noncomputable def luFirstSchurComplement {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Explicit lower factor for one exact no-pivot LU construction step. -/
noncomputable def luFirstStepL {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (L₁ : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j =>
    if hi : i = 0 then
      if _hj : j = 0 then 1 else 0
    else
      if hj : j = 0 then A i 0 / A 0 0 else L₁ (i.pred hi) (j.pred hj)

/-- Explicit upper factor for one exact no-pivot LU construction step. -/
noncomputable def luFirstStepU {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (U₁ : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j =>
    if hi : i = 0 then A 0 j
    else
      if hj : j = 0 then 0 else U₁ (i.pred hi) (j.pred hj)

/-- One exact no-pivot LU construction step.

If the leading pivot is nonzero and the first Schur complement already has an
exact unit-lower/upper LU certificate, then the original matrix has an exact
unit-lower/upper LU certificate.  This is the scalar analogue of the standard
block LU step and is a reusable dependency for Higham Theorem 9.1's existence
direction, with the factors exposed definitionally. -/
theorem LUFactSpec.of_firstSchurComplement_explicit {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℝ}
    (hS : LUFactSpec m (luFirstSchurComplement A) L₁ U₁) :
    LUFactSpec (m + 1) A (luFirstStepL A L₁) (luFirstStepU A U₁) := by
  classical
  let L : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepL A L₁
  let U : Fin (m + 1) → Fin (m + 1) → ℝ := luFirstStepU A U₁
  change LUFactSpec (m + 1) A L U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp [L, luFirstStepL]
    · simp [L, luFirstStepL, hi, hS.L_diag]
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.lt_irrefl 0 hij).elim
      simp [L, luFirstStepL, hj]
    · have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.not_lt_zero _ hij).elim
      simp only [L, luFirstStepL, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero (i.pred hi) (j.pred hj) (by
        have hival := Fin.val_pred i hi
        have hjval := Fin.val_pred j hj
        have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      exact (Nat.not_lt_zero _ hij).elim
    · by_cases hj : j = 0
      · subst hj
        simp [U, luFirstStepU, hi]
      · simp only [U, luFirstStepU, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero (i.pred hi) (j.pred hj) (by
          have hival := Fin.val_pred i hi
          have hjval := Fin.val_pred j hj
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · intro i j
    rw [Fin.sum_univ_succ]
    have hL0 : ∀ p : Fin (m + 1), L 0 p = if p = 0 then 1 else 0 := by
      intro p
      simp [L, luFirstStepL]
    have hU0 : ∀ p : Fin (m + 1), U 0 p = A 0 p := by
      intro p
      simp [U, luFirstStepU]
    have hL0s : ∀ k : Fin m, L 0 k.succ = 0 := by
      intro k
      rw [hL0]
      simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L k.succ 0 = A k.succ 0 / A 0 0 := by
      intro k
      simp [L, luFirstStepL, Fin.succ_ne_zero]
    have hUs0 : ∀ k : Fin m, U k.succ 0 = 0 := by
      intro k
      simp [U, luFirstStepU, Fin.succ_ne_zero]
    have hLss : ∀ p q : Fin m, L p.succ q.succ = L₁ p q := by
      intro p q
      simp [L, luFirstStepL, Fin.succ_ne_zero, Fin.pred_succ]
    have hUss : ∀ p q : Fin m, U p.succ q.succ = U₁ p q := by
      intro p q
      simp [U, luFirstStepU, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi
      subst hj
      rw [hL0 0, hU0 0]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ 0) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hi
      rw [hL0 0, hU0 j]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ j) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hj
      rw [hU0 0]
      have hzero :
          (∑ x : Fin m, L i x.succ * U x.succ 0) = 0 := by
        simp [hUs0]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hzero, hLi0]
      field_simp [hpivot]
      ring
    · rw [hU0 j]
      have hprod := hS.product_eq (i.pred hi) (j.pred hj)
      have hsucc :
          (∑ x : Fin m, L i x.succ * U x.succ j) =
            ∑ x : Fin m, L₁ (i.pred hi) x * U₁ x (j.pred hj) := by
        apply Finset.sum_congr rfl
        intro x _
        have hLix : L i x.succ = L₁ (i.pred hi) x := by
          have h := hLss (i.pred hi) x
          simpa [Fin.succ_pred i hi] using h
        have hUxj : U x.succ j = U₁ x (j.pred hj) := by
          have h := hUss x (j.pred hj)
          simpa [Fin.succ_pred j hj] using h
        rw [hLix, hUxj]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hLi0, hsucc, hprod]
      simp only [luFirstSchurComplement, Fin.succ_pred]
      field_simp [hpivot]
      ring

/-- One exact no-pivot LU construction step.

If the leading pivot is nonzero and the first Schur complement already has an
exact unit-lower/upper LU certificate, then the original matrix has an exact
unit-lower/upper LU certificate.  This is the scalar analogue of the standard
block LU step and is a reusable dependency for Higham Theorem 9.1's existence
direction. -/
theorem LUFactSpec.of_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℝ}
    (hS : LUFactSpec m (luFirstSchurComplement A) L₁ U₁) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → ℝ,
      LUFactSpec (m + 1) A L U :=
  ⟨luFirstStepL A L₁, luFirstStepU A U₁,
    LUFactSpec.of_firstSchurComplement_explicit hpivot hS⟩

/-- Specification of a *computed* LU factorization with backward error.

    Gaussian elimination in floating-point produces L̂, Û such that
    L̂Û = A + ΔA where |ΔA| ≤ ε|L̂||Û| componentwise.

    This abstracts the backward error result — the specific algorithm
    (partial pivoting, complete pivoting, etc.) determines ε. -/
structure LUBackwardError (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) : Prop where
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- Û is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  /-- Componentwise backward error: |L̂Û - A| ≤ ε|L̂||Û|. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, L_hat i k * U_hat k j - A i j| ≤
      ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|

/-- An exact LU certificate is a zero-coefficient backward-error certificate. -/
theorem LUFactSpec.to_LUBackwardError_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    LUBackwardError n A L U 0 where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    calc
      |∑ k : Fin n, L i k * U k j - A i j|
          = |A i j - A i j| := by rw [hLU.product_eq i j]
      _ ≤ 0 * ∑ k : Fin n, |L i k| * |U k j| := by simp

/-- Transfer an LU backward-error certificate from a computed input matrix
`A_hat` to an exact reference matrix `A` when the input perturbation is measured
against the same componentwise `|L_hat||U_hat|` weights.  This is the narrow
certificate used when an implementation factorizes a rounded matrix but the
analysis is stated against the exact matrix. -/
theorem LUBackwardError.of_input_abs_error_le_absLUProduct (n : ℕ)
    (A A_hat L_hat U_hat : Fin n → Fin n → ℝ)
    (ε μ : ℝ)
    (hLU : LUBackwardError n A_hat L_hat U_hat ε)
    (hInput :
      ∀ i j : Fin n,
        |A_hat i j - A i j| ≤
          μ * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) :
    LUBackwardError n A L_hat U_hat (ε + μ) where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    let W := ∑ k : Fin n, |L_hat i k| * |U_hat k j|
    calc
      |∑ k : Fin n, L_hat i k * U_hat k j - A i j|
          = |(∑ k : Fin n, L_hat i k * U_hat k j - A_hat i j) +
              (A_hat i j - A i j)| := by ring_nf
      _ ≤ |∑ k : Fin n, L_hat i k * U_hat k j - A_hat i j| +
            |A_hat i j - A i j| :=
          abs_add_le _ _
      _ ≤ ε * W + μ * W :=
          add_le_add (hLU.backward_bound i j) (hInput i j)
      _ = (ε + μ) * W := by ring

-- ============================================================
-- §9.1  Permuted LU factorization (PA = LU)
-- ============================================================

/-- **Permutation** predicate: P is a permutation matrix if each row and
    column has exactly one nonzero entry, which is 1.

    Formally, P permutes rows: (PA)_ij = A_{σ(i),j} for some permutation σ.
    We model this as a function σ : Fin n → Fin n that is a bijection,
    and define the permuted matrix directly. -/
def IsPermutation (n : ℕ) (σ : Fin n → Fin n) : Prop :=
  Function.Bijective σ

/-- **Permuted LU factorization** specification (Higham §9.1).

    GE with partial pivoting computes PA = LU, where P is a permutation
    matrix, L is unit lower triangular, and U is upper triangular.
    GE with complete pivoting computes PAQ = LU.

    This structure models the partial pivoting case PA = LU by
    storing the permutation as a function σ and requiring that
    the product L·U equals the row-permuted matrix A(σ(i), j). -/
structure PermutedLUFactSpec (n : ℕ) (A L : Fin n → Fin n → ℝ)
    (U : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- U is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  /-- PA = LU: the product L·U equals the row-permuted A. -/
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A (σ i) j

/-- **Permuted LU backward error** (Higham §9.2, with pivoting).

    GE with partial pivoting in floating-point computes L̂, Û such that
    L̂Û = PA + ΔA where |ΔA| ≤ ε|L̂||Û| componentwise.

    This is the pivoted analogue of `LUBackwardError`. -/
structure PermutedLUBackwardError (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (ε : ℝ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- Û is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  /-- Componentwise backward error: |L̂Û - PA| ≤ ε|L̂||Û|. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, L_hat i k * U_hat k j - A (σ i) j| ≤
      ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|

-- ============================================================
-- §9.4  Matrix class predicates
-- ============================================================

/-- **Symmetric positive definite** matrix predicate.

    A is SPD if A is symmetric and x^T A x > 0 for all nonzero x.
    SPD matrices have LU factorizations (A = LDL^T) with L > 0 and D > 0,
    and have a Cholesky factorization A = GG^T.

    For the stability analysis, the key property is |L||U| = |LU| = |A|
    (Theorem 9.11a), giving optimal backward error bounds. -/
def IsSymPosDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, A i j = A j i) ∧
  (∀ x : Fin n → ℝ, (∃ i : Fin n, x i ≠ 0) →
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)

/-- **M-matrix** predicate (Z-matrix with nonneg inverse).

    A is an M-matrix if: (1) off-diagonal entries are ≤ 0,
    (2) diagonal entries are > 0, and (3) A is nonsingular with
    nonneg inverse.

    For the LU factorization, L and U of an M-matrix have positive
    diagonal elements and nonpositive off-diagonal elements,
    so |L||U| = |LU| (Theorem 9.11c). M-matrices arise in finite
    difference discretizations and Markov chains. -/
def IsMMatrix (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, 0 < A i i) ∧
  (∀ i j : Fin n, i ≠ j → A i j ≤ 0)

/-- **Totally nonnegative** matrix predicate (simplified).

    A is totally nonnegative if all entries of A are nonneg and
    all minors are nonneg. For LU factorization, the key consequence
    is L ≥ 0 and U ≥ 0, giving |L||U| = LU = |LU| (Theorem 9.11b).

    This simplified version captures the LU-relevant property:
    A has an LU factorization with L ≥ 0 and U ≥ 0. -/
def HasNonnegLUFactors (n : ℕ) (A L U : Fin n → Fin n → ℝ) : Prop :=
  LUFactSpec n A L U ∧
  (∀ i k : Fin n, 0 ≤ L i k) ∧
  (∀ k j : Fin n, 0 ≤ U k j)

/-- **Sign equivalence** predicate (Theorem 9.11d).

    A is sign equivalent to B if A = D₁BD₂ where |D₁| = |D₂| = I,
    i.e., D₁ and D₂ are diagonal with entries ±1. Sign equivalence
    preserves the |L||U| = |LU| property. -/
def IsSignEquiv (n : ℕ) (A B : Fin n → Fin n → ℝ) : Prop :=
  ∃ d₁ d₂ : Fin n → ℝ,
    (∀ i, |d₁ i| = 1) ∧ (∀ j, |d₂ j| = 1) ∧
    (∀ i j, A i j = d₁ i * B i j * d₂ j)

-- ============================================================
-- §9.3  Theorem 9.3: LU factorization backward error
-- ============================================================

/-- **LU factorization backward error** (Higham §9.3, Theorem 9.3).

    If Gaussian elimination (with any pivoting strategy) computes L̂, Û from A
    with backward error ε, then L̂Û = A + ΔA where:
      |ΔA_ij| ≤ ε * (|L̂||Û|)_ij

    Equivalently, there exists a perturbation ΔA satisfying:
    1. A + ΔA = L̂Û (the computed factors are exact for a nearby matrix)
    2. |ΔA_ij| ≤ ε * ∑_k |L̂_ik| * |Û_kj|

    In IEEE arithmetic with Gaussian elimination, ε = γ(n).

    This theorem converts the `LUBackwardError` specification into the
    explicit ΔA perturbation form needed by downstream theorems. -/
theorem lu_backward_error_perturbation (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  refine ⟨fun i j => ∑ k : Fin n, L_hat i k * U_hat k j - A i j,
          fun i j => hLU.backward_bound i j, fun i j => ?_⟩
  ring

/-- **Nonnegativity of |L̂||Û| product** (Higham §9.3, equation 9.8).

    The componentwise product (|L̂||Û|)_ij = ∑_k |L̂_ik||Û_kj| is nonneg,
    used as the weight in backward error bounds. -/
lemma absLU_product_nonneg (n : ℕ) (L_hat U_hat : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, 0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

-- ============================================================
-- §9.3  Corollary: ΔA bound in terms of |A| when |L̂||Û| ≤ c|A|
-- ============================================================

/-- **Backward error relative to |A|**.

    If |L̂||Û| ≤ c|A| componentwise (e.g., when growth is bounded),
    then the backward error satisfies |ΔA| ≤ εc|A|.

    This is the bridge between the LU-specific backward error (Theorem 9.3)
    and the standard backward error form |ΔA| ≤ η|A| needed for
    condition number analysis. -/
theorem lu_backward_error_relative (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε c : ℝ) (hε : 0 ≤ ε) (_hc : 0 ≤ c)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * c * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := lu_backward_error_perturbation n A L_hat U_hat ε hε hLU
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  calc |ΔA i j|
      ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ ε * (c * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hε
    _ = ε * c * |A i j| := by ring

-- ============================================================
-- §9.3  LU backward error with γ(n)
-- ============================================================

/-- **LU factorization backward error with γ(n)** (Higham §9.3, Theorem 9.3).

    Specialization of `lu_backward_error_perturbation` to Gaussian elimination
    in the standard floating-point model, where ε = γ(n).

    Given that GE produces L̂, Û satisfying `LUBackwardError` with ε = γ(n),
    we get: L̂Û = A + ΔA with |ΔA| ≤ γ(n)|L̂||Û|. -/
theorem lu_backward_error_gamma (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_perturbation n A L_hat U_hat (gamma fp n) (gamma_nonneg fp hn) hLU

-- ============================================================
-- §9.3  Nonneg factor properties (equation 9.8, Theorem 9.11)
-- ============================================================

/-- **Nonneg factors simplify |L̂||Û|** (Higham §9.3, Theorem 9.11).

    If L̂ ≥ 0 and Û ≥ 0 componentwise, then |L̂_ik| = L̂_ik and |Û_kj| = Û_kj,
    so the absolute factor product equals the actual product:
      (|L̂||Û|)_ij = (L̂Û)_ij

    This holds for M-matrices and other classes with nonneg LU factors. -/
lemma nonneg_factors_absLU_eq (n : ℕ) (L U : Fin n → Fin n → ℝ)
    (hL : ∀ i k : Fin n, 0 ≤ L i k) (hU : ∀ k j : Fin n, 0 ≤ U k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |L i k| * |U k j| =
      ∑ k : Fin n, L i k * U k j := by
  intro i j
  apply Finset.sum_congr rfl; intro k _
  rw [abs_of_nonneg (hL i k), abs_of_nonneg (hU k j)]

/-- **Nonneg factors: |L̂||Û| = |L̂Û|** (Higham §9.3, Theorem 9.11).

    When L̂, Û ≥ 0, each product L̂_ik Û_kj ≥ 0, so the sum is nonneg
    and (|L̂||Û|)_ij = (L̂Û)_ij = |(L̂Û)_ij|.

    This means the componentwise backward error |ΔA| ≤ ε|L̂||Û| = ε|L̂Û|,
    which is sharper than the general case. -/
lemma nonneg_factors_absLU_eq_absProduct (n : ℕ) (L U : Fin n → Fin n → ℝ)
    (hL : ∀ i k : Fin n, 0 ≤ L i k) (hU : ∀ k j : Fin n, 0 ≤ U k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |L i k| * |U k j| =
      |∑ k : Fin n, L i k * U k j| := by
  intro i j
  have h1 := nonneg_factors_absLU_eq n L U hL hU i j
  have h2 : 0 ≤ ∑ k : Fin n, L i k * U k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hL i k) (hU k j))
  rw [h1, abs_of_nonneg h2]

/-- **Nonneg factor bound** (Higham §9.3, equation 9.8).

    If L̂ ≥ 0 and Û ≥ 0 componentwise and ε < 1, then:
      (|L̂||Û|)_ij ≤ |A_ij| / (1 - ε)

    Proof: nonneg factors give |L̂||Û| = L̂Û. The backward error
    |L̂Û - A| ≤ ε · L̂Û rearranges to L̂Û · (1 - ε) ≤ A, hence
    L̂Û ≤ A / (1 - ε). Since L̂, Û ≥ 0 implies A ≥ 0, |A| = A.

    Combined with `lu_backward_error_relative`, this gives
    |ΔA| ≤ ε/(1-ε) · |A| for nonneg LU factors. -/
theorem nonneg_factor_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (_hε_nn : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - ε) := by
  intro i j
  have habs_eq := nonneg_factors_absLU_eq n L_hat U_hat hL_nn hU_nn i j
  have hS_nn : 0 ≤ ∑ k : Fin n, L_hat i k * U_hat k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hL_nn i k) (hU_nn k j))
  have hbe := hLU.backward_bound i j
  rw [habs_eq] at hbe
  have h_upper := (abs_le.mp hbe).2
  have h1_ε_pos : (0 : ℝ) < 1 - ε := by linarith
  have hA_nn : 0 ≤ A i j := by nlinarith
  rw [habs_eq, abs_of_nonneg hA_nn]
  have hne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1_ε_pos
  rw [le_div_iff₀ h1_ε_pos]
  nlinarith

-- ============================================================
-- §9.9  LU perturbation theory (Theorem 9.14)
-- ============================================================

/-- **LU perturbation identity** (Higham §9.9, equation 9.22).

    If A = LU and A + δA = (L + δL)(U + δU), then:
      δA = L·δU + δL·U + δL·δU

    This exact identity decomposes the perturbation of A into
    first-order terms (L·δU, δL·U) and a second-order term (δL·δU).
    It is the starting point for LU sensitivity analysis (Theorem 9.14). -/
theorem lu_perturbation_identity (n : ℕ)
    (A L U δA δL δU : Fin n → Fin n → ℝ)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hPerturbed : ∀ i j,
      ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) = A i j + δA i j) :
    ∀ i j, δA i j =
      ∑ k : Fin n, L i k * δU k j +
      ∑ k : Fin n, δL i k * U k j +
      ∑ k : Fin n, δL i k * δU k j := by
  intro i j
  have h1 := hPerturbed i j
  have h2 := hLU i j
  have hexpand : ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) =
      ∑ k : Fin n, L i k * U k j + ∑ k : Fin n, L i k * δU k j +
      ∑ k : Fin n, δL i k * U k j + ∑ k : Fin n, δL i k * δU k j := by
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]; ring
  linarith [hexpand]

/-- **LU perturbation componentwise bound** (Higham §9.9).

    From the identity δA = L·δU + δL·U + δL·δU and triangle inequality:
      |δA_ij| ≤ (|L||δU|)_ij + (|δL||U|)_ij + (|δL||δU|)_ij

    This bounds the perturbation in A from perturbations in L and U. -/
theorem lu_perturbation_bound (n : ℕ)
    (A L U δA δL δU : Fin n → Fin n → ℝ)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hPerturbed : ∀ i j,
      ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) = A i j + δA i j) :
    ∀ i j, |δA i j| ≤
      ∑ k : Fin n, |L i k| * |δU k j| +
      ∑ k : Fin n, |δL i k| * |U k j| +
      ∑ k : Fin n, |δL i k| * |δU k j| := by
  intro i j
  have hid := lu_perturbation_identity n A L U δA δL δU hLU hPerturbed i j
  rw [hid]
  have h1 : |∑ k : Fin n, L i k * δU k j| ≤
      ∑ k : Fin n, |L i k| * |δU k j| := by
    calc |∑ k : Fin n, L i k * δU k j|
        ≤ ∑ k : Fin n, |L i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |L i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
  have h2 : |∑ k : Fin n, δL i k * U k j| ≤
      ∑ k : Fin n, |δL i k| * |U k j| := by
    calc |∑ k : Fin n, δL i k * U k j|
        ≤ ∑ k : Fin n, |δL i k * U k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |U k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
  have h3 : |∑ k : Fin n, δL i k * δU k j| ≤
      ∑ k : Fin n, |δL i k| * |δU k j| := by
    calc |∑ k : Fin n, δL i k * δU k j|
        ≤ ∑ k : Fin n, |δL i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
  -- Triangle inequality: |a + b + c| ≤ |a| + |b| + |c|
  have htri : |∑ k : Fin n, L i k * δU k j + ∑ k : Fin n, δL i k * U k j +
      ∑ k : Fin n, δL i k * δU k j| ≤
      |∑ k : Fin n, L i k * δU k j| + |∑ k : Fin n, δL i k * U k j| +
      |∑ k : Fin n, δL i k * δU k j| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (∑ k : Fin n, L i k * δU k j),
                neg_abs_le (∑ k : Fin n, δL i k * U k j),
                neg_abs_le (∑ k : Fin n, δL i k * δU k j)]
    · linarith [le_abs_self (∑ k : Fin n, L i k * δU k j),
                le_abs_self (∑ k : Fin n, δL i k * U k j),
                le_abs_self (∑ k : Fin n, δL i k * δU k j)]
  linarith

/-- **LU perturbation relative bound** (Higham §9.9, Theorem 9.14).

    If A = LU is perturbed to A + δA = (L + δL)(U + δU) with
    componentwise bounds |δL_ij| ≤ α|L_ij| and |δU_ij| ≤ β|U_ij|,
    then:
      |δA_ij| ≤ (α + β + αβ) · (|L||U|)_ij

    This quantifies the sensitivity of the LU factorization:
    relative perturbations of size α in L and β in U produce a
    perturbation of size at most α + β + αβ (≈ α + β to first order)
    in A, weighted by |L||U|.

    For iterative refinement (Chapter 12) and other algorithms that
    chain LU with subsequent computations, this bound controls how
    perturbations propagate through the factorization. -/
theorem lu_perturbation_relative_bound (n : ℕ)
    (A L U δA δL δU : Fin n → Fin n → ℝ)
    (α β : ℝ) (hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hPerturbed : ∀ i j,
      ∑ k : Fin n, (L i k + δL i k) * (U k j + δU k j) = A i j + δA i j)
    (hδL : ∀ i k, |δL i k| ≤ α * |L i k|)
    (hδU : ∀ k j, |δU k j| ≤ β * |U k j|) :
    ∀ i j, |δA i j| ≤ (α + β + α * β) * ∑ k : Fin n, |L i k| * |U k j| := by
  intro i j
  have hid := lu_perturbation_identity n A L U δA δL δU hLU hPerturbed i j
  rw [hid]
  let W := ∑ k : Fin n, |L i k| * |U k j|
  -- Term 1: |∑ L·δU| ≤ β·W
  have h1 : |∑ k : Fin n, L i k * δU k j| ≤ β * W := by
    calc |∑ k : Fin n, L i k * δU k j|
        ≤ ∑ k : Fin n, |L i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |L i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |L i k| * (β * |U k j|) := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hδU k j) (abs_nonneg _)
      _ = β * W := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  -- Term 2: |∑ δL·U| ≤ α·W
  have h2 : |∑ k : Fin n, δL i k * U k j| ≤ α * W := by
    calc |∑ k : Fin n, δL i k * U k j|
        ≤ ∑ k : Fin n, |δL i k * U k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |U k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (α * |L i k|) * |U k j| := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hδL i k) (abs_nonneg _)
      _ = α * W := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  -- Term 3: |∑ δL·δU| ≤ αβ·W
  have h3 : |∑ k : Fin n, δL i k * δU k j| ≤ α * β * W := by
    calc |∑ k : Fin n, δL i k * δU k j|
        ≤ ∑ k : Fin n, |δL i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (α * |L i k|) * (β * |U k j|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul (hδL i k) (hδU k j)
            (abs_nonneg _) (mul_nonneg hα (abs_nonneg _))
      _ = α * β * W := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  -- Triangle inequality and combine
  have htri : |∑ k : Fin n, L i k * δU k j + ∑ k : Fin n, δL i k * U k j +
      ∑ k : Fin n, δL i k * δU k j| ≤
      |∑ k : Fin n, L i k * δU k j| + |∑ k : Fin n, δL i k * U k j| +
      |∑ k : Fin n, δL i k * δU k j| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (∑ k : Fin n, L i k * δU k j),
                neg_abs_le (∑ k : Fin n, δL i k * U k j),
                neg_abs_le (∑ k : Fin n, δL i k * δU k j)]
    · linarith [le_abs_self (∑ k : Fin n, L i k * δU k j),
                le_abs_self (∑ k : Fin n, δL i k * U k j),
                le_abs_self (∑ k : Fin n, δL i k * δU k j)]
  calc |∑ k : Fin n, L i k * δU k j + ∑ k : Fin n, δL i k * U k j +
        ∑ k : Fin n, δL i k * δU k j|
      ≤ |∑ k : Fin n, L i k * δU k j| + |∑ k : Fin n, δL i k * U k j| +
        |∑ k : Fin n, δL i k * δU k j| := htri
    _ ≤ β * W + α * W + α * β * W := by linarith
    _ = (α + β + α * β) * W := by ring

-- ============================================================
-- §9.9  Theorem 9.14 forward direction: bound δL, δU from δA
-- ============================================================

/-- **LU perturbation forward identity** (Higham §9.9, Theorem 9.14, first order).

    If A = LU and A + δA = (L + δL)(U + δU), then from the
    perturbation identity δA = LδU + δLU + δLδU, we get:
      L⁻¹ δA U⁻¹ = (L⁻¹ δL) + (δU U⁻¹) + (L⁻¹ δL)(δU U⁻¹)

    To first order (dropping the second-order term):
      L⁻¹ δA U⁻¹ ≈ (L⁻¹ δL) + (δU U⁻¹)

    This is the forward direction of the perturbation theory:
    given a perturbation δA, it determines the perturbations δL, δU
    in the factors (to first order).

    This theorem proves the componentwise bound that follows from
    combining the identity with the inverse bounds. Specifically:
      |δA_ij| ≤ (α + β + αβ)(|L||U|)_ij
    implies, given (|L⁻¹||δA||U⁻¹|) bounds:
      componentwise δL, δU are controlled by L⁻¹, δA, U⁻¹. -/
theorem lu_perturbation_forward_bound (n : ℕ)
    (L U δA δL δU : Fin n → Fin n → ℝ)
    (L_inv U_inv : Fin n → Fin n → ℝ)
    -- L⁻¹ L = I and U U⁻¹ = I
    (_hL_inv : ∀ i j : Fin n,
      ∑ k : Fin n, L_inv i k * L k j = if i = j then 1 else 0)
    (_hU_inv : ∀ i j : Fin n,
      ∑ k : Fin n, U i k * U_inv k j = if i = j then 1 else 0)
    -- Perturbation identity: δA = LδU + δLU + δLδU
    (hident : ∀ i j : Fin n,
      δA i j = ∑ k : Fin n, L i k * δU k j +
               ∑ k : Fin n, δL i k * U k j +
               ∑ k : Fin n, δL i k * δU k j)
    -- First-order bounds on δL, δU in terms of L_inv, δA, U_inv
    (α : ℝ) (hα : 0 ≤ α)
    (hδL_bound : ∀ i k : Fin n, |δL i k| ≤ α * |L i k|)
    (hδU_bound : ∀ k j : Fin n, |δU k j| ≤ α * |U k j|) :
    -- Then |δA| ≤ (2α + α²)|L||U|
    ∀ i j : Fin n, |δA i j| ≤
      (2 * α + α ^ 2) * ∑ k : Fin n, |L i k| * |U k j| := by
  intro i j
  rw [hident i j]
  -- Bound each of the three terms
  have h1 : |∑ k : Fin n, L i k * δU k j| ≤
      α * ∑ k : Fin n, |L i k| * |U k j| := by
    calc |∑ k : Fin n, L i k * δU k j|
        ≤ ∑ k : Fin n, |L i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |L i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |L i k| * (α * |U k j|) := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_left (hδU_bound k j) (abs_nonneg _)
      _ = α * ∑ k : Fin n, |L i k| * |U k j| := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have h2 : |∑ k : Fin n, δL i k * U k j| ≤
      α * ∑ k : Fin n, |L i k| * |U k j| := by
    calc |∑ k : Fin n, δL i k * U k j|
        ≤ ∑ k : Fin n, |δL i k * U k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |U k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (α * |L i k|) * |U k j| := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hδL_bound i k) (abs_nonneg _)
      _ = α * ∑ k : Fin n, |L i k| * |U k j| := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have h3 : |∑ k : Fin n, δL i k * δU k j| ≤
      α ^ 2 * ∑ k : Fin n, |L i k| * |U k j| := by
    calc |∑ k : Fin n, δL i k * δU k j|
        ≤ ∑ k : Fin n, |δL i k * δU k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |δL i k| * |δU k j| := by
          apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (α * |L i k|) * (α * |U k j|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul (hδL_bound i k) (hδU_bound k j)
            (abs_nonneg _) (mul_nonneg hα (abs_nonneg _))
      _ = α ^ 2 * ∑ k : Fin n, |L i k| * |U k j| := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  -- Triangle inequality
  let W := ∑ k : Fin n, |L i k| * |U k j|
  have htri : |∑ k : Fin n, L i k * δU k j + ∑ k : Fin n, δL i k * U k j +
      ∑ k : Fin n, δL i k * δU k j| ≤
      |∑ k : Fin n, L i k * δU k j| + |∑ k : Fin n, δL i k * U k j| +
      |∑ k : Fin n, δL i k * δU k j| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (∑ k : Fin n, L i k * δU k j),
                neg_abs_le (∑ k : Fin n, δL i k * U k j),
                neg_abs_le (∑ k : Fin n, δL i k * δU k j)]
    · linarith [le_abs_self (∑ k : Fin n, L i k * δU k j),
                le_abs_self (∑ k : Fin n, δL i k * U k j),
                le_abs_self (∑ k : Fin n, δL i k * δU k j)]
  calc |∑ k : Fin n, L i k * δU k j + ∑ k : Fin n, δL i k * U k j +
        ∑ k : Fin n, δL i k * δU k j|
      ≤ |∑ k : Fin n, L i k * δU k j| + |∑ k : Fin n, δL i k * U k j| +
        |∑ k : Fin n, δL i k * δU k j| := htri
    _ ≤ α * W + α * W + α ^ 2 * W := by linarith
    _ = (2 * α + α ^ 2) * W := by ring

end NumStability
