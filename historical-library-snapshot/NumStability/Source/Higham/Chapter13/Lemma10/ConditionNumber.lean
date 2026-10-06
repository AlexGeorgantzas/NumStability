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
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds

/-!
# Source.Higham.Chapter13.Lemma10.ConditionNumber

This module formalizes the source-facing Chapter 13 statements for
`Lemma10.ConditionNumber`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Conditional adapter for **Lemma 13.10** (Higham): if the SPD Schur-complement
    condition-number route supplies the bound, expose the source-facing result.
    If A is SPD, the Schur complement
    S = A₂₂ − A₂₁ A₁₁⁻¹ A₂₁ᵀ satisfies κ₂(S) ≤ κ₂(A). -/
theorem higham13_lemma13_10_conditional_bound
    (kappa2_S kappa2_A : ℝ) (hBound : kappa2_S ≤ kappa2_A) :
    kappa2_S ≤ kappa2_A := hBound

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 proof route:
    source-positive-definite block version of the Schur-complement
    condition-number comparison.

    This composes the proved `||S||₂ <= ||A||₂` certificate with the
    source-indexed Schur inverse certificate at radius
    `||nonsingInv (r+s) A||₂`.  The remaining source-facing wrapper is to
    derive the displayed block hypotheses directly from `IsSymPosDef (r+s) A`
    and the standard source block definitions. -/
theorem higham13_lemma13_10_schur_kappa_bound_of_source_posDef_block
    {r s : ℕ} [Nonempty (Fin s)]
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    (hFull : (Matrix.fromBlocks A11 A21ᵀ A21 A22).PosDef)
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A21ᵀ =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))) :
    kappa2
      (fun i j : Fin s => (A22 - A21 * A11⁻¹ * A21ᵀ) i j)
      (fun i j : Fin s =>
        ((A22 - A21 * A11⁻¹ * A21ᵀ)⁻¹ :
          Matrix (Fin s) (Fin s) ℝ) i j)
      ≤ kappa2 A (nonsingInv (r + s) A) := by
  classical
  let S : Fin s → Fin s → ℝ :=
    fun i j => (A22 - A21 * A11⁻¹ * A21ᵀ) i j
  let Sinv : Fin s → Fin s → ℝ :=
    fun i j =>
      ((A22 - A21 * A11⁻¹ * A21ᵀ)⁻¹ :
        Matrix (Fin s) (Fin s) ℝ) i j
  have hFull_eq :
      Matrix.fromBlocks A11 A21ᵀ A21 A22 =
        (fun i j : Fin r ⊕ Fin s =>
          A (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA11_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA12_block i) j
            simpa [Matrix.fromBlocks] using h
    | inr i =>
        cases j with
        | inl j =>
            have h := congr_fun (congr_fun hA21_block i) j
            simpa [Matrix.fromBlocks] using h
        | inr j =>
            have h := congr_fun (congr_fun hA22_block i) j
            simpa [Matrix.fromBlocks] using h
  have hAblock :
      finiteOpNorm2Le
        (fun i j : Fin r ⊕ Fin s =>
          (Matrix.fromBlocks A11 A21ᵀ A21 A22) i j)
        (opNorm2 A) := by
    have hA_reindex :
        finiteOpNorm2Le
          (fun i j : Fin r ⊕ Fin s => A (finSumFinEquiv i) (finSumFinEquiv j))
          (opNorm2 A) :=
      finiteOpNorm2Le_reindex_equiv
        (e := (finSumFinEquiv : (Fin r ⊕ Fin s) ≃ Fin (r + s)))
        A
        (finiteOpNorm2Le_of_opNorm2Le A (opNorm2Le_opNorm2 A))
    simpa [hFull_eq] using hA_reindex
  have hSfin :
      finiteOpNorm2Le S (opNorm2 A) := by
    simpa [S] using
      higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound
        A11 A21 A22 hFull hAblock
  have hSinvfin :
      finiteOpNorm2Le Sinv (opNorm2 (nonsingInv (r + s) A)) := by
    simpa [S, Sinv] using
      higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse
        A A11 A21 A22 hFull
        hA11_block hA12_block hA21_block hA22_block
  exact
    kappa2_le_of_opNorm2Le_bounds_general
      S Sinv A (nonsingInv (r + s) A)
      (opNorm2Le_of_finiteOpNorm2Le S hSfin)
      (opNorm2Le_of_finiteOpNorm2Le Sinv hSinvfin)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10:
    if the source block matrix `A` is symmetric positive definite, then the
    Schur complement
    `S = A₂₂ - A₂₁ A₁₁⁻¹ A₂₁ᵀ` satisfies `κ₂(S) ≤ κ₂(A)`.

    The blocks are the standard leading/trailing blocks induced by
    `finSumFinEquiv`, and both condition numbers use the repository's
    source-facing exact 2-norm product with the canonical `nonsingInv`. -/
theorem higham13_lemma13_10_schur_kappa_bound_of_spd
    {r s : ℕ} [Nonempty (Fin s)]
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hSPD : IsSymPosDef (r + s) A) :
    let A11 : Matrix (Fin r) (Fin r) ℝ :=
      fun i j =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
    let A21 : Matrix (Fin s) (Fin r) ℝ :=
      fun i j =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
    let A22 : Matrix (Fin s) (Fin s) ℝ :=
      fun i j =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
    let S : Fin s → Fin s → ℝ :=
      fun i j => (A22 - A21 * A11⁻¹ * A21ᵀ) i j
    kappa2 S (nonsingInv s S) ≤ kappa2 A (nonsingInv (r + s) A) := by
  classical
  let A11 : Matrix (Fin r) (Fin r) ℝ :=
    fun i j =>
      A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
  let A21 : Matrix (Fin s) (Fin r) ℝ :=
    fun i j =>
      A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
  let A22 : Matrix (Fin s) (Fin s) ℝ :=
    fun i j =>
      A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
  let S : Fin s → Fin s → ℝ :=
    fun i j => (A22 - A21 * A11⁻¹ * A21ᵀ) i j
  change kappa2 S (nonsingInv s S) ≤
    kappa2 A (nonsingInv (r + s) A)
  have hFull_eq :
      Matrix.fromBlocks A11 A21ᵀ A21 A22 =
        (fun i j : Fin r ⊕ Fin s =>
          A (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            rfl
        | inr j =>
            exact hSPD.1
              (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
              (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
    | inr i =>
        cases j with
        | inl j =>
            rfl
        | inr j =>
            rfl
  have hFull : (Matrix.fromBlocks A11 A21ᵀ A21 A22).PosDef := by
    rw [hFull_eq]
    exact
      matrix_posDef_submatrix_of_injective
        (isSymPosDef_to_matrix_posDef A hSPD)
        (fun i : Fin r ⊕ Fin s => finSumFinEquiv i)
        finSumFinEquiv.injective
  have hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) := rfl
  have hA12_block : A21ᵀ =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) := by
    ext i j
    exact hSPD.1
      (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
  have hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) := rfl
  have hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) := rfl
  have hmain :=
    higham13_lemma13_10_schur_kappa_bound_of_source_posDef_block
      A A11 A21 A22 hFull
      hA11_block hA12_block hA21_block hA22_block
  simpa [S, nonsingInv] using hmain

end NumStability
