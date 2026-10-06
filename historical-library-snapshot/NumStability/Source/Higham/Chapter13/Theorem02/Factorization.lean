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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Source.Higham.Chapter13.Theorem02.Factorization

This module formalizes the source-facing Chapter 13 statements for
`Theorem02.Factorization`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Theorem 13.2:
    the leading `(p+1) × (p+1)` principal block submatrix of a uniform block
    matrix.  Lean's `p = 0` corresponds to the source's first leading block. -/
noncomputable def leadingBlockPrefix13_2 {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (p : ℕ) (hp : p < m) :
    Fin (p + 1) → Fin (p + 1) → (Fin r → Fin r → ℝ) :=
  fun i j =>
    A ⟨i.val, by
        have hi : i.val < p + 1 := i.isLt
        omega⟩
      ⟨j.val, by
        have hj : j.val < p + 1 := j.isLt
        omega⟩

/-- The flattened leading block prefix is the principal submatrix of the
    flattened full block matrix on the first block indices. -/
theorem blockMatrixFlat_leadingBlockPrefix13_2 {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (p : ℕ) (hp : p < m) :
    blockMatrixFlat (leadingBlockPrefix13_2 A p hp) =
      (blockMatrixFlat A).submatrix
        (fun is : Fin (p + 1) × Fin r =>
          (⟨is.1.val, by
              have hi : is.1.val < p + 1 := is.1.isLt
              omega⟩, is.2))
        (fun is : Fin (p + 1) × Fin r =>
          (⟨is.1.val, by
              have hi : is.1.val < p + 1 := is.1.isLt
              omega⟩, is.2)) := by
  ext is jt
  rcases is with ⟨i, s⟩
  rcases jt with ⟨j, t⟩
  simp [blockMatrixFlat, leadingBlockPrefix13_2]

/-- The all-leading-prefix nonsingularity table contains the full matrix when
    the block dimension is positive. -/
theorem higham13_blockMatrixNonsingular_of_all_leadingBlockPrefixes {m r : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp)) :
    BlockMatrixNonsingular A := by
  cases m with
  | zero =>
      exact False.elim ((Nat.lt_irrefl 0) hm)
  | succ m =>
      simpa [leadingBlockPrefix13_2] using hPrefix m (Nat.lt_succ_self m)

/-- Determinant form of the full-matrix certificate contained in an
    all-leading-prefix nonsingularity table, stated for the uniform
    `Fin (m*r)` flattening used by the Chapter 13 growth-factor API. -/
theorem higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
    {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp)) :
    Matrix.det (blockMatrixFlatFin A :
      Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0 := by
  exact
    det_ne_zero_blockMatrixFlatFin_of_blockMatrixNonsingular A
      (higham13_blockMatrixNonsingular_of_all_leadingBlockPrefixes
        hm A hPrefix)

/-- Higham, 2nd ed., Chapter 13, §13.3.2:
    if the flattened full block matrix is positive definite, then every leading
    block prefix is positive definite after flattening. -/
theorem leadingBlockPrefix13_2_posDef_flat_of_posDef_flat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (p : ℕ) (hp : p < m)
    (hPos : Matrix.PosDef (blockMatrixFlat A)) :
    Matrix.PosDef (blockMatrixFlat (leadingBlockPrefix13_2 A p hp)) := by
  rw [blockMatrixFlat_leadingBlockPrefix13_2 A p hp]
  exact matrix_posDef_submatrix_of_injective hPos
    (fun is : Fin (p + 1) × Fin r =>
      (⟨is.1.val, by
          have hi : is.1.val < p + 1 := is.1.isLt
          omega⟩, is.2))
    (by
      intro x y hxy
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun z : Fin m × Fin r => z.1.val) hxy
      · exact congrArg (fun z : Fin m × Fin r => z.2) hxy)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2:
    the source condition that the first `m-1` leading principal block
    submatrices are nonsingular.  For a matrix with `m` block rows/columns, this
    asks for nonsingularity of prefixes of block sizes `1, ..., m-1`. -/
def LeadingPrincipalBlockNonsingular13_2 {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) : Prop :=
  ∀ p : ℕ, (hp : p + 1 < m) →
    BlockMatrixNonsingular
      (leadingBlockPrefix13_2 A p (Nat.lt_trans (Nat.lt_succ_self p) hp))

/-- Higham, 2nd ed., Chapter 13, §13.3.2:
    positive definiteness of the flattened block matrix supplies the
    leading-principal-block nonsingularity condition used by Theorem 13.2.

    This proves the source prose "SPD matrices have block LU because all
    leading principal submatrices are nonsingular" at the repository's uniform
    block-matrix model level. -/
theorem LeadingPrincipalBlockNonsingular13_2.of_posDef_flat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hPos : Matrix.PosDef (blockMatrixFlat A)) :
    LeadingPrincipalBlockNonsingular13_2 A := by
  intro p hp
  exact blockMatrixNonsingular_of_posDef_flat
    (leadingBlockPrefix13_2 A p (Nat.lt_trans (Nat.lt_succ_self p) hp))
    (leadingBlockPrefix13_2_posDef_flat_of_posDef_flat A p
      (Nat.lt_trans (Nat.lt_succ_self p) hp) hPos)

private lemma sum_fin_prefix_eq_of_tail_zero {q m : ℕ}
    (hqm : q ≤ m) (f : Fin m → ℝ)
    (hzero : ∀ k : Fin m, q ≤ k.val → f k = 0) :
    ∑ k : Fin q, f (Fin.castLE hqm k) = ∑ k : Fin m, f k := by
  let g : ℕ → ℝ := fun n => if hn : n < m then f ⟨n, hn⟩ else 0
  have hleft :
      (∑ k : Fin q, f (Fin.castLE hqm k)) =
        ∑ n ∈ Finset.range q, g n := by
    calc
      (∑ k : Fin q, f (Fin.castLE hqm k)) = ∑ k : Fin q, g k.val := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hkm : k.val < m := Nat.lt_of_lt_of_le k.isLt hqm
        have hk_eq : Fin.castLE hqm k = (⟨k.val, hkm⟩ : Fin m) := Fin.ext rfl
        simp [g, hkm, hk_eq]
      _ = ∑ n ∈ Finset.range q, g n := Fin.sum_univ_eq_sum_range g q
  have hright :
      (∑ k : Fin m, f k) = ∑ n ∈ Finset.range m, g n := by
    calc
      (∑ k : Fin m, f k) = ∑ k : Fin m, g k.val := by
        apply Finset.sum_congr rfl
        intro k _hk
        simp [g, k.isLt]
      _ = ∑ n ∈ Finset.range m, g n := Fin.sum_univ_eq_sum_range g m
  have hsubset : Finset.range q ⊆ Finset.range m := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hn) hqm)
  have hsum_subset :
      ∑ n ∈ Finset.range q, g n = ∑ n ∈ Finset.range m, g n := by
    apply Finset.sum_subset hsubset
    intro n hn_m hn_not_q
    have hnm : n < m := Finset.mem_range.mp hn_m
    have hqn : q ≤ n := Nat.le_of_not_gt (by
      intro hnq
      exact hn_not_q (Finset.mem_range.mpr hnq))
    simp [g, hnm, hzero ⟨n, hnm⟩ hqn]
  rw [hleft, hright]
  exact hsum_subset

private lemma leadingBlockPrefix13_2_apply_castLE {m r : ℕ}
    {B : Fin m → Fin m → (Fin r → Fin r → ℝ)}
    {p : ℕ} (hp : p < m) (hle : p + 1 ≤ m)
    (i j : Fin (p + 1)) :
    leadingBlockPrefix13_2 B p hp i j =
      B (Fin.castLE hle i) (Fin.castLE hle j) := by
  unfold leadingBlockPrefix13_2
  congr

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse-side dependency:
    any block LU factorization restricts to a block LU factorization of each
    leading principal block prefix.

    This is the structural bridge needed before uniqueness of a full
    factorization can be pushed down to the leading submatrices appearing in
    the theorem. -/
theorem BlockLUFactSpec.of_leadingBlockPrefix13_2 {m r : ℕ}
    {A L U : Fin m → Fin m → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec m r A L U)
    (p : ℕ) (hp : p < m) :
    BlockLUFactSpec (p + 1) r
      (leadingBlockPrefix13_2 A p hp)
      (leadingBlockPrefix13_2 L p hp)
      (leadingBlockPrefix13_2 U p hp) := by
  let hle : p + 1 ≤ m := Nat.succ_le_of_lt hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [leadingBlockPrefix13_2] using hLU.L_diag (Fin.castLE hle i)
  · intro i j hij
    exact hLU.L_upper_zero (Fin.castLE hle i) (Fin.castLE hle j) (by simpa using hij)
  · intro i j hij
    exact hLU.U_lower_zero (Fin.castLE hle i) (Fin.castLE hle j) (by simpa using hij)
  · intro i j s t
    let term : Fin m → ℝ := fun k =>
      ∑ l : Fin r, L (Fin.castLE hle i) k s l * U k (Fin.castLE hle j) l t
    have htail_zero : ∀ k : Fin m, p + 1 ≤ k.val → term k = 0 := by
      intro k hk
      have hlt : (Fin.castLE hle i).val < k.val := by
        exact Nat.lt_of_lt_of_le i.isLt hk
      have hLzero : L (Fin.castLE hle i) k = zeroBlock r :=
        hLU.L_upper_zero (Fin.castLE hle i) k hlt
      simp [term, hLzero, zeroBlock]
    have hsum :
        ∑ k : Fin (p + 1), term (Fin.castLE hle k) =
          ∑ k : Fin m, term k :=
      sum_fin_prefix_eq_of_tail_zero hle term htail_zero
    have hprod :
        ∑ k : Fin m, term k =
          A (Fin.castLE hle i) (Fin.castLE hle j) s t := by
      simpa [term] using hLU.product_eq (Fin.castLE hle i) (Fin.castLE hle j) s t
    calc
      ∑ k : Fin (p + 1),
          ∑ l : Fin r,
            leadingBlockPrefix13_2 L p hp i k s l *
              leadingBlockPrefix13_2 U p hp k j l t
          = ∑ k : Fin (p + 1), term (Fin.castLE hle k) := by
              simp_rw [leadingBlockPrefix13_2_apply_castLE hp hle]
              rfl
      _ = ∑ k : Fin m, term k := hsum
      _ = A (Fin.castLE hle i) (Fin.castLE hle j) s t := hprod
      _ = leadingBlockPrefix13_2 A p hp i j s t := by
              rw [leadingBlockPrefix13_2_apply_castLE hp hle]

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 dependency:
    from nonsingularity of the first leading principal block submatrix, extract
    the two-sided inverse data for the leading block `A₁₁`.  This is the bridge
    from the source condition to the one-step Schur-complement construction. -/
theorem LeadingPrincipalBlockNonsingular13_2.first_block_inverse {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hm : 0 < m)
    (hlead : LeadingPrincipalBlockNonsingular13_2 A) :
    ∃ A11_inv : Fin r → Fin r → ℝ,
      (∀ s t : Fin r,
        ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0) ∧
      (∀ s t : Fin r,
        ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) := by
  have hprefix :
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 A 0 (Nat.lt_trans (Nat.lt_succ_self 0)
          (by simpa using Nat.succ_lt_succ hm))) :=
    hlead 0 (by simpa using Nat.succ_lt_succ hm)
  rcases hprefix with ⟨Ainv, hInv⟩
  refine ⟨Ainv 0 0, ?_, ?_⟩
  · intro s t
    have h := hInv.1 0 0 s t
    rw [Fin.sum_univ_one] at h
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using h
  · intro s t
    have h := hInv.2 0 0 s t
    rw [Fin.sum_univ_one] at h
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using h

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 induction bookkeeping:
    the leading prefix of the Schur complement is the Schur complement of the
    next larger leading prefix.  This is the index bridge needed to transfer
    leading-principal-block nonsingularity down the recursive Schur step. -/
theorem leadingBlockPrefix13_2_blockSchur {m r : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (p : ℕ) (hp : p < m + 1) :
    leadingBlockPrefix13_2 (blockSchur A A11_inv) p hp =
      blockSchur
        (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hp))
        A11_inv := by
  ext i j s t
  simp [leadingBlockPrefix13_2, blockSchur]

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 induction dependency:
    if a block matrix is nonsingular and its leading block has the supplied
    two-sided inverse, then the Schur complement is nonsingular.

    The inverse of the Schur complement is the lower-right block of a two-sided
    inverse of the full block matrix.  The proof uses `Matrix.of` internally to
    force Lean's reducible matrix type to use inner matrix multiplication rather
    than pointwise function multiplication on raw function-valued blocks. -/
theorem blockSchur_nonsingular_of_nonsingular_of_first_block_inverse {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hA : BlockMatrixNonsingular A) :
    BlockMatrixNonsingular (blockSchur A A11_inv) := by
  classical
  rcases hA with ⟨Ainv, hInv⟩
  let A00 : Matrix (Fin 1) (Fin 1) (Matrix (Fin r) (Fin r) ℝ) :=
    fun _ _ => Matrix.of (A 0 0)
  let P : Matrix (Fin 1) (Fin 1) (Matrix (Fin r) (Fin r) ℝ) :=
    fun _ _ => Matrix.of A11_inv
  let B : Matrix (Fin 1) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
    fun _ j => Matrix.of (A 0 (Fin.succ j))
  let C : Matrix (Fin m) (Fin 1) (Matrix (Fin r) (Fin r) ℝ) :=
    fun i _ => Matrix.of (A (Fin.succ i) 0)
  let D : Matrix (Fin m) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
    fun i j => Matrix.of (A (Fin.succ i) (Fin.succ j))
  let G : Matrix (Fin m) (Fin 1) (Matrix (Fin r) (Fin r) ℝ) :=
    fun i _ => Matrix.of (Ainv (Fin.succ i) 0)
  let F : Matrix (Fin 1) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
    fun _ j => Matrix.of (Ainv 0 (Fin.succ j))
  let H : Matrix (Fin m) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
    fun i j => Matrix.of (Ainv (Fin.succ i) (Fin.succ j))
  let S : Matrix (Fin m) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
    fun i j => Matrix.of (blockSchur A A11_inv i j)
  have hS : S = D - C * P * B := by
    ext i j s t
    have hCPB :
        (C * P * B) i j s t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A (Fin.succ i) 0 s l₁ * A11_inv l₁ l₂ *
              A 0 (Fin.succ j) l₂ t := by
      simp only [C, P, B, Matrix.mul_apply, Fin.sum_univ_one, Matrix.sum_apply]
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l₁ _hl₁
      apply Finset.sum_congr rfl
      intro l₂ _hl₂
      simp
    change blockSchur A A11_inv i j s t = D i j s t - (C * P * B) i j s t
    rw [hCPB]
    simp [D, blockSchur]
  have hA00P : A00 * P = 1 := by
    ext i j s t
    fin_cases i
    fin_cases j
    simpa [A00, P, Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply, idBlock,
      Matrix.sum_apply, Finset.sum_apply]
      using hInvRight s t
  have hPA00 : P * A00 = 1 := by
    ext i j s t
    fin_cases i
    fin_cases j
    simpa [A00, P, Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply, idBlock,
      Matrix.sum_apply, Finset.sum_apply]
      using hInvLeft s t
  have hG_A00_H_C : G * A00 + H * C = 0 := by
    ext i j s t
    fin_cases j
    have h := hInv.1 (Fin.succ i) 0 s t
    rw [Fin.sum_univ_succ] at h
    simpa [G, A00, H, C, Matrix.mul_apply, Matrix.add_apply, Matrix.zero_apply,
      blockMatrixIdentity, zeroBlock, Fin.sum_univ_one, Matrix.sum_apply,
      Finset.sum_apply, Pi.add_apply] using h
  have hG_B_H_D : G * B + H * D = 1 := by
    ext i j s t
    have h := hInv.1 (Fin.succ i) (Fin.succ j) s t
    rw [Fin.sum_univ_succ] at h
    simpa [G, B, H, D, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
      blockMatrixIdentity, idBlock, zeroBlock, Fin.sum_univ_one, Matrix.sum_apply,
      Finset.sum_apply, Pi.add_apply] using h
  have hA00_F_B_H : A00 * F + B * H = 0 := by
    ext i j s t
    fin_cases i
    have h := hInv.2 0 (Fin.succ j) s t
    rw [Fin.sum_univ_succ] at h
    simpa [A00, F, B, H, Matrix.mul_apply, Matrix.add_apply, Matrix.zero_apply,
      blockMatrixIdentity, zeroBlock, Fin.sum_univ_one, Matrix.sum_apply,
      Finset.sum_apply, Pi.add_apply] using h
  have hC_F_D_H : C * F + D * H = 1 := by
    ext i j s t
    have h := hInv.2 (Fin.succ i) (Fin.succ j) s t
    rw [Fin.sum_univ_succ] at h
    simpa [C, F, D, H, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
      blockMatrixIdentity, idBlock, zeroBlock, Fin.sum_univ_one, Matrix.sum_apply,
      Finset.sum_apply, Pi.add_apply] using h
  have hHC : H * C = -(G * A00) := by
    rw [← add_eq_zero_iff_eq_neg]
    simpa [add_comm] using hG_A00_H_C
  have hBH : B * H = -(A00 * F) := by
    rw [← add_eq_zero_iff_eq_neg]
    simpa [add_comm] using hA00_F_B_H
  have hHS : H * S = 1 := by
    rw [hS]
    calc
      H * (D - C * P * B) = H * D - H * (C * P * B) := by
        exact Matrix.mul_sub H D (C * P * B)
      _ = H * D - (H * C) * P * B := by
        rw [← Matrix.mul_assoc H (C * P) B, ← Matrix.mul_assoc H C P]
      _ = H * D - (-(G * A00)) * P * B := by
        rw [hHC]
      _ = H * D + G * (A00 * P) * B := by
        have hneg : (-(G * A00)) * P * B = -((G * A00) * P * B) := by
          calc
            (-(G * A00)) * P * B = (-((G * A00) * P)) * B := by
              exact congrArg (fun X => X * B) (Matrix.neg_mul (G * A00) P)
            _ = -((G * A00) * P * B) := by
              exact Matrix.neg_mul ((G * A00) * P) B
        rw [hneg, sub_neg_eq_add, Matrix.mul_assoc G A00 P]
      _ = H * D + G * B := by
        rw [hA00P]
        simp
      _ = G * B + H * D := by
        rw [add_comm]
      _ = 1 := hG_B_H_D
  have hSH : S * H = 1 := by
    rw [hS]
    calc
      (D - C * P * B) * H = D * H - (C * P * B) * H := by
        exact Matrix.sub_mul D (C * P * B) H
      _ = D * H - C * P * (B * H) := by
        rw [Matrix.mul_assoc (C * P) B H]
      _ = D * H - C * P * (-(A00 * F)) := by
        rw [hBH]
      _ = D * H + C * (P * A00) * F := by
        have hneg : C * P * (-(A00 * F)) = -(C * P * (A00 * F)) := by
          exact Matrix.mul_neg (C * P) (A00 * F)
        rw [hneg, sub_neg_eq_add]
        rw [← Matrix.mul_assoc (C * P) A00 F, Matrix.mul_assoc C P A00]
      _ = D * H + C * F := by
        rw [hPA00]
        simp
      _ = C * F + D * H := by
        rw [add_comm]
      _ = 1 := hC_F_D_H
  refine ⟨fun i j => H i j, ?_, ?_⟩
  · intro i j s t
    have hblock := congr_fun (congr_fun hHS i) j
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [S, H, Matrix.mul_apply, Matrix.sum_apply, Finset.sum_apply,
      blockMatrixIdentity, idBlock, zeroBlock, Matrix.one_apply] using hscalar
  · intro i j s t
    have hblock := congr_fun (congr_fun hSH i) j
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [S, H, Matrix.mul_apply, Matrix.sum_apply, Finset.sum_apply,
      blockMatrixIdentity, idBlock, zeroBlock, Matrix.one_apply] using hscalar

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse-side dependency:
    if the first block has the supplied two-sided inverse and the Schur
    complement is nonsingular, then the whole one-step block matrix is
    nonsingular.

    The proof flattens the trailing block rows/columns to a scalar matrix over
    `ℝ`, applies Mathlib's Schur-complement invertibility theorem there, and
    then unflattens the inverse back to the chapter's uniform-block predicate. -/
theorem blockMatrixNonsingular_of_first_block_inverse_of_blockSchur_nonsingular {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hSchur : BlockMatrixNonsingular (blockSchur A A11_inv)) :
    BlockMatrixNonsingular A := by
  classical
  rcases hSchur with ⟨Sinv, hSinv⟩
  let A00 : Matrix (Fin r) (Fin r) ℝ := Matrix.of (A 0 0)
  let P : Matrix (Fin r) (Fin r) ℝ := Matrix.of A11_inv
  let B : Matrix (Fin r) (Fin m × Fin r) ℝ :=
    fun s jt => A 0 (Fin.succ jt.1) s jt.2
  let C : Matrix (Fin m × Fin r) (Fin r) ℝ :=
    fun is t => A (Fin.succ is.1) 0 is.2 t
  let D : Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ :=
    fun is jt => A (Fin.succ is.1) (Fin.succ jt.1) is.2 jt.2
  let S : Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ :=
    fun is jt => blockSchur A A11_inv is.1 jt.1 is.2 jt.2
  let H : Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ :=
    fun is jt => Sinv is.1 jt.1 is.2 jt.2
  have hS_eq : S = D - C * P * B := by
    ext is jt
    rcases is with ⟨i, s⟩
    rcases jt with ⟨j, t⟩
    have hCPB :
        (C * P * B) (i, s) (j, t) =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A (Fin.succ i) 0 s l₁ * A11_inv l₁ l₂ *
              A 0 (Fin.succ j) l₂ t := by
      simp only [C, P, B, Matrix.mul_apply]
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l₁ _hl₁
      apply Finset.sum_congr rfl
      intro l₂ _hl₂
      simp
    change blockSchur A A11_inv i j s t =
      D (i, s) (j, t) - (C * P * B) (i, s) (j, t)
    rw [hCPB]
    simp [D, blockSchur]
  have hA00P : A00 * P = 1 := by
    ext s t
    simpa [A00, P, Matrix.mul_apply, Matrix.one_apply] using hInvRight s t
  have hPA00 : P * A00 = 1 := by
    ext s t
    simpa [A00, P, Matrix.mul_apply, Matrix.one_apply] using hInvLeft s t
  letI : Invertible A00 := {
    invOf := P
    invOf_mul_self := hPA00
    mul_invOf_self := hA00P
  }
  have hHS : H * S = 1 := by
    ext is jt
    rcases is with ⟨i, s⟩
    rcases jt with ⟨j, t⟩
    have h := hSinv.1 i j s t
    have hId :
        (if i = j then idBlock r else zeroBlock r) s t =
          if i = j ∧ s = t then 1 else 0 := by
      by_cases hij : i = j <;> by_cases hst : s = t <;>
        simp [hij, hst, idBlock, zeroBlock]
    simpa [H, S, Matrix.mul_apply, Fintype.sum_prod_type, blockMatrixIdentity,
      idBlock, zeroBlock, Matrix.one_apply, Prod.ext_iff, hId] using h
  have hSH : S * H = 1 := by
    ext is jt
    rcases is with ⟨i, s⟩
    rcases jt with ⟨j, t⟩
    have h := hSinv.2 i j s t
    have hId :
        (if i = j then idBlock r else zeroBlock r) s t =
          if i = j ∧ s = t then 1 else 0 := by
      by_cases hij : i = j <;> by_cases hst : s = t <;>
        simp [hij, hst, idBlock, zeroBlock]
    simpa [H, S, Matrix.mul_apply, Fintype.sum_prod_type, blockMatrixIdentity,
      idBlock, zeroBlock, Matrix.one_apply, Prod.ext_iff, hId] using h
  let iS : Invertible S := {
    invOf := H
    invOf_mul_self := hHS
    mul_invOf_self := hSH
  }
  letI : Invertible (D - C * ⅟A00 * B) :=
    Invertible.copy iS _ (by
      change D - C * P * B = S
      exact hS_eq.symm)
  let M : Matrix (Fin r ⊕ (Fin m × Fin r)) (Fin r ⊕ (Fin m × Fin r)) ℝ :=
    Matrix.fromBlocks A00 B C D
  letI : Invertible M := Matrix.fromBlocks₁₁Invertible A00 B C D
  let Ainv : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j s t =>
    if hi : i = 0 then
      if hj : j = 0 then
        (⅟M) (Sum.inl s) (Sum.inl t)
      else
        (⅟M) (Sum.inl s) (Sum.inr (j.pred hj, t))
    else
      if hj : j = 0 then
        (⅟M) (Sum.inr (i.pred hi, s)) (Sum.inl t)
      else
        (⅟M) (Sum.inr (i.pred hi, s)) (Sum.inr (j.pred hj, t))
  refine ⟨Ainv, ?_, ?_⟩
  · intro i j s t
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst i
      subst j
      have h := congr_fun (congr_fun (invOf_mul_self M) (Sum.inl s)) (Sum.inl t)
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply] using h
    · subst i
      have h := congr_fun (congr_fun (invOf_mul_self M) (Sum.inl s))
        (Sum.inr (j.pred hj, t))
      have h0j : (0 : Fin (m + 1)) ≠ j := fun h0j => hj h0j.symm
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, h0j, hj, Fin.succ_pred j hj] using h
    · subst j
      have h := congr_fun (congr_fun (invOf_mul_self M) (Sum.inr (i.pred hi, s)))
        (Sum.inl t)
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, hi, Fin.succ_pred i hi] using h
    · have h := congr_fun (congr_fun (invOf_mul_self M) (Sum.inr (i.pred hi, s)))
        (Sum.inr (j.pred hj, t))
      have hBlockId :
          (if i = j then idBlock r else zeroBlock r) s t =
            if i = j ∧ s = t then 1 else 0 := by
        by_cases hij : i = j <;> by_cases hst : s = t <;>
          simp [hij, hst, idBlock, zeroBlock]
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, hi, hj, Fin.succ_pred i hi,
        Fin.succ_pred j hj, Prod.ext_iff, hBlockId] using h
  · intro i j s t
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst i
      subst j
      have h := congr_fun (congr_fun (mul_invOf_self M) (Sum.inl s)) (Sum.inl t)
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply] using h
    · subst i
      have h := congr_fun (congr_fun (mul_invOf_self M) (Sum.inl s))
        (Sum.inr (j.pred hj, t))
      have h0j : (0 : Fin (m + 1)) ≠ j := fun h0j => hj h0j.symm
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, h0j, hj, Fin.succ_pred j hj] using h
    · subst j
      have h := congr_fun (congr_fun (mul_invOf_self M) (Sum.inr (i.pred hi, s)))
        (Sum.inl t)
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, hi, Fin.succ_pred i hi] using h
    · have h := congr_fun (congr_fun (mul_invOf_self M) (Sum.inr (i.pred hi, s)))
        (Sum.inr (j.pred hj, t))
      have hBlockId :
          (if i = j then idBlock r else zeroBlock r) s t =
            if i = j ∧ s = t then 1 else 0 := by
        by_cases hij : i = j <;> by_cases hst : s = t <;>
          simp [hij, hst, idBlock, zeroBlock]
      simpa [Ainv, M, A00, B, C, D, Matrix.mul_apply, Matrix.fromBlocks,
        Fin.sum_univ_succ, Fintype.sum_prod_type, blockMatrixIdentity, idBlock,
        zeroBlock, Matrix.one_apply, hi, hj, Fin.succ_pred i hi,
        Fin.succ_pred j hj, Prod.ext_iff, hBlockId] using h

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 induction dependency:
    leading-principal-block nonsingularity transfers from a full block matrix
    to the Schur complement after eliminating the first block. -/
theorem LeadingPrincipalBlockNonsingular13_2.schur {m r : ℕ}
    {A : Fin (m + 2) → Fin (m + 2) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hlead : LeadingPrincipalBlockNonsingular13_2 A) :
    LeadingPrincipalBlockNonsingular13_2 (blockSchur A A11_inv) := by
  intro p hp
  have hpPrefix : p < m + 1 := Nat.lt_trans (Nat.lt_succ_self p) hp
  have hA_prefix :
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpPrefix)) := by
    simpa [leadingBlockPrefix13_2] using
      hlead (p + 1) (by
        have := Nat.succ_lt_succ hp
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
  have hInvLeft_prefix :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          A11_inv s l *
            leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpPrefix) 0 0 l t =
          if s = t then 1 else 0 := by
    intro s t
    simpa [leadingBlockPrefix13_2] using hInvLeft s t
  have hInvRight_prefix :
      ∀ s t : Fin r,
        ∑ l : Fin r,
          leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpPrefix) 0 0 s l *
            A11_inv l t =
          if s = t then 1 else 0 := by
    intro s t
    simpa [leadingBlockPrefix13_2] using hInvRight s t
  have hSchur_prefix :
      BlockMatrixNonsingular
        (blockSchur
          (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpPrefix))
          A11_inv) :=
    blockSchur_nonsingular_of_nonsingular_of_first_block_inverse
      (A := leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpPrefix))
      (A11_inv := A11_inv)
      hInvLeft_prefix hInvRight_prefix hA_prefix
  rw [leadingBlockPrefix13_2_blockSchur A A11_inv p hpPrefix]
  exact hSchur_prefix

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse dependency:
    a two-sided inverse for the first block makes the first leading principal
    block submatrix nonsingular.  This closes the base prefix in the
    Schur-tail-to-full leading-principal-block assembly step. -/
theorem leadingBlockPrefix13_2_zero_nonsingular_of_first_block_inverse {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) :
    BlockMatrixNonsingular (leadingBlockPrefix13_2 A 0 (Nat.succ_pos m)) := by
  refine ⟨fun _ _ => A11_inv, ?_, ?_⟩
  · intro i j s t
    fin_cases i
    fin_cases j
    rw [Fin.sum_univ_one]
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using hInvLeft s t
  · intro i j s t
    fin_cases i
    fin_cases j
    rw [Fin.sum_univ_one]
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using hInvRight s t

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse dependency:
    if the first block is nonsingular and the Schur complement has all required
    leading principal block submatrices nonsingular, then the original matrix
    has all required leading principal block submatrices nonsingular.

    This is the reverse of `LeadingPrincipalBlockNonsingular13_2.schur` at the
    level of the source condition; the remaining converse-side bottleneck is
    deriving the first-block inverse from uniqueness of the full block LU
    factorization. -/
theorem LeadingPrincipalBlockNonsingular13_2.of_first_block_inverse_of_schur
    {m r : ℕ}
    {A : Fin (m + 2) → Fin (m + 2) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hSchurLead : LeadingPrincipalBlockNonsingular13_2 (blockSchur A A11_inv)) :
    LeadingPrincipalBlockNonsingular13_2 A := by
  intro p hp
  cases p with
  | zero =>
      have h0 :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 A 0 (Nat.succ_pos (m + 1))) :=
        leadingBlockPrefix13_2_zero_nonsingular_of_first_block_inverse
          (A := A) (A11_inv := A11_inv) hInvLeft hInvRight
      simpa [leadingBlockPrefix13_2] using h0
  | succ p =>
      have hpTail : p + 1 < m + 1 := by omega
      have hpSchur : p < m + 1 := Nat.lt_trans (Nat.lt_succ_self p) hpTail
      have hTailPrefix :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 (blockSchur A A11_inv) p hpSchur) :=
        hSchurLead p hpTail
      have hSchurPrefix :
          BlockMatrixNonsingular
            (blockSchur
              (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur))
              A11_inv) := by
        rw [← leadingBlockPrefix13_2_blockSchur A A11_inv p hpSchur]
        exact hTailPrefix
      have hInvLeftPrefix :
          ∀ s t : Fin r,
            ∑ l : Fin r,
              A11_inv s l *
                leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur) 0 0 l t =
              if s = t then 1 else 0 := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvLeft s t
      have hInvRightPrefix :
          ∀ s t : Fin r,
            ∑ l : Fin r,
              leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur) 0 0 s l *
                A11_inv l t =
              if s = t then 1 else 0 := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvRight s t
      have hAssembled :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur)) :=
        blockMatrixNonsingular_of_first_block_inverse_of_blockSchur_nonsingular
          (A := leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur))
          (A11_inv := A11_inv)
          hInvLeftPrefix hInvRightPrefix hSchurPrefix
      simpa [leadingBlockPrefix13_2] using hAssembled

/-- The all-leading-prefix nonsingularity table also supplies the positive
    first-split max-entry denominator used by the local Schur-step APIs. -/
theorem maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
    {m r : ℕ} (hN : 0 < r + m * r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp)) :
    0 < maxEntryNorm hN (blockMatrixFirstSplitFlat A) := by
  exact
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat A)
      (det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A
        (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
          (Nat.succ_pos m) (fun i j a b => A i j a b) hPrefix))

end NumStability
