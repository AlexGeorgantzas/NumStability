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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization

/-!
# Source.Higham.Chapter13.Section01.StandardFactorization

This module formalizes the source-facing Chapter 13 statements for
`Section01.StandardFactorization`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Adjust the block upper factor after factoring each diagonal block
    `Uᵢᵢ = Lbarᵢ Ubarᵢ`.  The diagonal blocks become `Ubarᵢ`; every block in
    block row `i` is premultiplied by `Lbarᵢ⁻¹`. -/
noncomputable def higham13_standardUpperFromBlockUpper
    {ι r α : Type*} [DecidableEq ι] [DecidableEq r] [Fintype r] [Fintype ι]
    [CommRing α]
    (Lbar Ubar : ι → Matrix r r α) [∀ i, Invertible (Lbar i)]
    (U : Matrix (r × ι) (r × ι) α) :
    Matrix (r × ι) (r × ι) α :=
  fun si tj =>
    if _h : si.2 = tj.2 then Ubar si.2 si.1 tj.1
    else
      let B : Matrix r r α := fun s t => U (s, si.2) (t, tj.2)
      ((⅟(Lbar si.2) : Matrix r r α) * B) si.1 tj.1

/-- Higham, 2nd ed., Chapter 13, Section 13.1, p.247:
    diagonal-block LU factorizations refine a block upper factor.

    If each diagonal block of the block upper factor `U` satisfies
    `Uᵢᵢ = Lbarᵢ Ubarᵢ`, then the block-diagonal matrix with blocks `Lbarᵢ`
    times the adjusted upper factor reconstructs `U`. -/
theorem higham13_block_upper_refinement_eq
    {ι r α : Type*} [DecidableEq ι] [DecidableEq r] [Fintype r] [Fintype ι]
    [CommRing α]
    (Lbar Ubar : ι → Matrix r r α) [∀ i, Invertible (Lbar i)]
    (U : Matrix (r × ι) (r × ι) α)
    (hdiag : ∀ i : ι, Lbar i * Ubar i = fun s t => U (s, i) (t, i)) :
    Matrix.blockDiagonal Lbar * higham13_standardUpperFromBlockUpper Lbar Ubar U = U := by
  ext si tj
  rcases si with ⟨s, i⟩
  rcases tj with ⟨t, j⟩
  rw [blockDiagonal_mul_apply_block]
  by_cases hij : i = j
  · subst j
    have h := congr_fun (congr_fun (hdiag i) s) t
    simpa [Matrix.mul_apply, higham13_standardUpperFromBlockUpper] using h
  · let B : Matrix r r α := fun a b => U (a, i) (b, j)
    have hmat : Lbar i * ((⅟(Lbar i) : Matrix r r α) * B) = B := by
      simp
    have h := congr_fun (congr_fun hmat s) t
    simpa [Matrix.mul_apply, higham13_standardUpperFromBlockUpper, hij, B] using h

/-- Higham, 2nd ed., Chapter 13, Section 13.1, p.247:
    relation between block LU and standard LU factorizations.

    Given a flattened block LU product `A = L U` and LU factorizations
    `Uᵢᵢ = Lbarᵢ Ubarᵢ` for each diagonal block of `U`, the same matrix factors
    as `(L diag(Lbarᵢ))` times the adjusted upper factor.  This is the exact
    product identity behind the prose statement; triangularity of the two
    refined factors is deliberately left to the caller's lower/upper-triangular
    hypotheses. -/
theorem higham13_block_lu_to_standard_lu_product
    {ι r α : Type*} [DecidableEq ι] [DecidableEq r] [Fintype r] [Fintype ι]
    [CommRing α]
    (A L U : Matrix (r × ι) (r × ι) α)
    (Lbar Ubar : ι → Matrix r r α) [∀ i, Invertible (Lbar i)]
    (hA : A = L * U)
    (hdiag : ∀ i : ι, Lbar i * Ubar i = fun s t => U (s, i) (t, i)) :
    A =
      (L * Matrix.blockDiagonal Lbar) *
        higham13_standardUpperFromBlockUpper Lbar Ubar U := by
  calc
    A = L * U := hA
    _ = L * (Matrix.blockDiagonal Lbar *
          higham13_standardUpperFromBlockUpper Lbar Ubar U) := by
        rw [higham13_block_upper_refinement_eq Lbar Ubar U hdiag]
    _ = (L * Matrix.blockDiagonal Lbar) *
          higham13_standardUpperFromBlockUpper Lbar Ubar U := by
        rw [Matrix.mul_assoc]

end NumStability
