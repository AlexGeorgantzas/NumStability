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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Source.Higham.Chapter13.Section01.NormConventions

This module formalizes the source-facing Chapter 13 statements for
`Section01.NormConventions`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- For the repository's block representation `Fin r → Fin r → ℝ`, the
    ambient Pi norm is exactly Higham's Chapter 13 entrywise max norm.  This
    lets Algorithm 13.3 Schur-stage blocks, whose norm table is defined using
    `‖·‖`, feed the Eq.13.21 max-entry growth bridge. -/
theorem higham13_block_norm_eq_maxEntryNorm {r : ℕ} (hr : 0 < r)
    (B : Fin r → Fin r → ℝ) :
    ‖B‖ = maxEntryNorm hr B := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (maxEntryNorm_nonneg hr B)]
    intro s
    rw [pi_norm_le_iff_of_nonneg (maxEntryNorm_nonneg hr B)]
    intro t
    simpa [Real.norm_eq_abs] using entry_le_maxEntryNorm hr B s t
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro s _hs
    apply Finset.sup'_le
    intro t _ht
    have hentry_row : ‖B s t‖ ≤ ‖B s‖ := norm_le_pi_norm (B s) t
    have hrow_all : ‖B s‖ ≤ ‖B‖ := norm_le_pi_norm B s
    simpa [Real.norm_eq_abs] using le_trans hentry_row hrow_all

/-- If a Chapter 13 block has zero ambient Pi norm, then every scalar entry of
    the block is zero. -/
theorem higham13_block_entries_zero_of_norm_eq_zero {r : ℕ}
    {B : Fin r → Fin r → ℝ} (hB : ‖B‖ = 0) :
    ∀ s t : Fin r, B s t = 0 := by
  have hzero : B = 0 := norm_eq_zero.mp hB
  intro s t
  exact congr_fun (congr_fun hzero s) t

/-- Finite block supremum for an arbitrary normed block type.

    This is the source-norm analogue of `blockMaxNorm`: it records
    `max_{i,j} ‖Aᵢⱼ‖` for whichever subordinate block norm is carried by the
    block type. -/
noncomputable def higham13_blockNormSup {m : ℕ} (hm : 0 < m)
    {α : Type*} [Norm α] (A : Fin m → Fin m → α) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j => ‖A i j‖))

lemma higham13_block_norm_le_blockNormSup {m : ℕ} (hm : 0 < m)
    {α : Type*} [Norm α] (A : Fin m → Fin m → α) (i j : Fin m) :
    ‖A i j‖ ≤ higham13_blockNormSup hm A := by
  unfold higham13_blockNormSup
  exact le_trans
    (Finset.le_sup' (fun j' => ‖A i j'‖) (Finset.mem_univ j))
    (Finset.le_sup' (fun i' =>
      Finset.sup' Finset.univ
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
        (fun j' => ‖A i' j'‖)) (Finset.mem_univ i))

lemma higham13_blockNormSup_nonneg {m : ℕ} (hm : 0 < m)
    {α : Type*} [SeminormedAddCommGroup α] (A : Fin m → Fin m → α) :
    0 ≤ higham13_blockNormSup hm A :=
  le_trans (norm_nonneg (A ⟨0, hm⟩ ⟨0, hm⟩))
    (higham13_block_norm_le_blockNormSup hm A ⟨0, hm⟩ ⟨0, hm⟩)

lemma higham13_blockNormSup_le_of_norm_le {m : ℕ} (hm : 0 < m)
    {α : Type*} [Norm α] (A : Fin m → Fin m → α) {C : ℝ}
    (hC : ∀ i j : Fin m, ‖A i j‖ ≤ C) :
    higham13_blockNormSup hm A ≤ C := by
  unfold higham13_blockNormSup
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  exact hC i j

/-- Higham, 2nd ed., Chapter 13, §13.1 norm convention:
    the block representation's max norm is definitionally the maximum over
    block indices and within-block indices, matching the chapter's
    entrywise `max |aᵢⱼ|` convention. -/
theorem higham13_norm_convention_blockMaxNorm_eq_entrywise_sup {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr A =
      Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
        (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
          (fun j => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
            (fun s => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
              (fun t => |A i j s t|)))) := by
  rfl

/-- Chapter 13 route audit for the matrix-`∞` branch.

    The reverse dimension-free comparison from the blockwise matrix-`∞`
    maximum to the chapter's entrywise block max norm is false already for one
    `2 x 2` block: the block with first row `[1, 1]` has entrywise max norm
    `1` but matrix-`∞` norm `2`.  Thus the current matrix-`∞` to entrywise
    max-norm transfer cannot remove its dimension factor without additional
    source structure. -/
theorem higham13_blockInfNorm_not_le_blockMaxNorm_counterexample :
    ∃ A : Fin 1 → Fin 1 → Matrix (Fin 2) (Fin 2) ℝ,
      blockMaxNorm (Nat.succ_pos 0) (Nat.succ_pos 1) A = 1 ∧
        blockInfNorm (Nat.succ_pos 0) A = 2 ∧
          ¬ blockInfNorm (Nat.succ_pos 0) A ≤
              blockMaxNorm (Nat.succ_pos 0) (Nat.succ_pos 1) A := by
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun s _ => if s = 0 then 1 else 0
  let A : Fin 1 → Fin 1 → Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => B
  have hBMax : maxEntryNorm (Nat.succ_pos 1) B = 1 := by
    apply le_antisymm
    · apply maxEntryNorm_le_of_entry_le_bound
      intro s t
      by_cases hs : s = 0
      · simp [B, hs]
      · simp [B, hs]
    · have h :=
        entry_le_maxEntryNorm (Nat.succ_pos 1) B (0 : Fin 2) (0 : Fin 2)
      norm_num [B] at h
      exact h
  have hBInf : infNorm B = 2 := by
    apply le_antisymm
    · apply infNorm_le_of_row_sum_le
      · intro s
        fin_cases s
        · norm_num [B]
        · norm_num [B]
      · norm_num
    · have h := row_sum_le_infNorm B (0 : Fin 2)
      norm_num [B] at h
      exact h
  have hMax : blockMaxNorm (Nat.succ_pos 0) (Nat.succ_pos 1) A = 1 := by
    apply le_antisymm
    · apply blockMaxNorm_le_of_entry_abs_le
      intro i j s t
      by_cases hs : s = 0
      · simp [A, B, hs]
      · simp [A, B, hs]
    · have h :=
        block_entry_abs_le_blockMaxNorm (Nat.succ_pos 0) (Nat.succ_pos 1)
          A (0 : Fin 1) (0 : Fin 1) (0 : Fin 2) (0 : Fin 2)
      norm_num [A, B] at h
      exact h
  have hInf : blockInfNorm (Nat.succ_pos 0) A = 2 := by
    apply le_antisymm
    · apply blockInfNorm_le_of_block_le
      intro i j
      simpa [A] using le_of_eq hBInf
    · have h :=
        block_le_blockInfNorm (Nat.succ_pos 0) A (0 : Fin 1) (0 : Fin 1)
      simpa [A, hBInf] using h
  refine ⟨A, hMax, hInf, ?_⟩
  intro h
  rw [hInf, hMax] at h
  norm_num at h

/-- Matrix-`∞` submultiplicativity for Mathlib matrix multiplication.

    The repository's base theorem is stated for the local `matMul`; this thin
    wrapper lets the Chapter 13 block-matrix route use ordinary `Matrix.mul`. -/
theorem infNorm_matrix_mul_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) ℝ) :
    infNorm (A * B) ≤ infNorm A * infNorm B := by
  simpa [matMul, Matrix.mul_apply] using
    (infNorm_matMul_le hr (fun i j => A i j) (fun i j => B i j))

/-- Aggregate column-mass budget after multiplying every active lower block by
    the pivot inverse in the matrix-`∞` norm. -/
theorem higham13_sum_infNorm_matrix_mul_pivot_le_of_column_mass
    {m r : ℕ} (hr : 0 < r) (tail : Finset (Fin m))
    (Acol : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) {gamma : ℝ}
    (hMass : ∑ i ∈ tail, infNorm (Acol i) ≤ gamma)
    (hPivot : infNorm P * gamma ≤ 1) :
    ∑ i ∈ tail, infNorm (Acol i * P) ≤ 1 := by
  have hterm :
      ∑ i ∈ tail, infNorm (Acol i * P) ≤
        ∑ i ∈ tail, infNorm (Acol i) * infNorm P := by
    apply Finset.sum_le_sum
    intro i _hi
    exact infNorm_matrix_mul_le hr (Acol i) P
  have hsum_mul :
      ∑ i ∈ tail, infNorm (Acol i) * infNorm P =
        (∑ i ∈ tail, infNorm (Acol i)) * infNorm P := by
    rw [Finset.sum_mul]
  have hscale :
      (∑ i ∈ tail, infNorm (Acol i)) * infNorm P ≤
        gamma * infNorm P :=
    mul_le_mul_of_nonneg_right hMass (infNorm_nonneg P)
  have hpivot_comm : gamma * infNorm P ≤ 1 := by
    calc
      gamma * infNorm P = infNorm P * gamma := by ring
      _ ≤ 1 := hPivot
  calc
    ∑ i ∈ tail, infNorm (Acol i * P)
        ≤ ∑ i ∈ tail, infNorm (Acol i) * infNorm P := hterm
    _ = (∑ i ∈ tail, infNorm (Acol i)) * infNorm P := hsum_mul
    _ ≤ gamma * infNorm P := hscale
    _ ≤ 1 := hpivot_comm

/-- Mixed aggregate triple-product budget for the column-BDD route.

    If the active pivot-column matrix-`∞` mass is bounded by `gamma` and the
    pivot inverse satisfies `||P||∞ * gamma <= 1`, then the whole active
    Schur-correction column contributes at most the pivot-row max-entry norm. -/
theorem higham13_sum_maxEntryNorm_matrix_mul_pivot_mul_le_of_column_mass
    {m r : ℕ} (hr : 0 < r) (tail : Finset (Fin m))
    (Acol : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (P R : Matrix (Fin r) (Fin r) ℝ) {gamma : ℝ}
    (hMass : ∑ i ∈ tail, infNorm (Acol i) ≤ gamma)
    (hPivot : infNorm P * gamma ≤ 1) :
    ∑ i ∈ tail, maxEntryNorm hr (Acol i * P * R) ≤
      maxEntryNorm hr R := by
  have hterm :
      ∑ i ∈ tail, maxEntryNorm hr (Acol i * P * R) ≤
        ∑ i ∈ tail, infNorm (Acol i * P) * maxEntryNorm hr R := by
    apply Finset.sum_le_sum
    intro i _hi
    exact maxEntryNorm_matrix_mul_le_infNorm_mul_maxEntryNorm hr (Acol i * P) R
  have hsum_mul :
      ∑ i ∈ tail, infNorm (Acol i * P) * maxEntryNorm hr R =
        (∑ i ∈ tail, infNorm (Acol i * P)) * maxEntryNorm hr R := by
    rw [Finset.sum_mul]
  have hmass :
      ∑ i ∈ tail, infNorm (Acol i * P) ≤ 1 :=
    higham13_sum_infNorm_matrix_mul_pivot_le_of_column_mass
      hr tail Acol P hMass hPivot
  have hmax_nonneg : 0 ≤ maxEntryNorm hr R := maxEntryNorm_nonneg hr R
  calc
    ∑ i ∈ tail, maxEntryNorm hr (Acol i * P * R)
        ≤ ∑ i ∈ tail, infNorm (Acol i * P) * maxEntryNorm hr R := hterm
    _ = (∑ i ∈ tail, infNorm (Acol i * P)) * maxEntryNorm hr R := hsum_mul
    _ ≤ 1 * maxEntryNorm hr R :=
        mul_le_mul_of_nonneg_right hmass hmax_nonneg
    _ = maxEntryNorm hr R := by ring

end NumStability
