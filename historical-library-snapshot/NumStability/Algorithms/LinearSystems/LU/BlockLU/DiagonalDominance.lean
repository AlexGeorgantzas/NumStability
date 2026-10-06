import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Block diagonal dominance

Reusable scalar definitions for column- and row-wise block diagonal dominance,
including the associated gamma margins.
-/

namespace NumStability

open scoped BigOperators

/-- **Block diagonal dominance by columns** (Higham, 2nd ed., eq. 13.17):
    ‖A_{jj}⁻¹‖⁻¹ − ∑_{i≠j} ‖A_{ij}‖ = γ_j ≥ 0. -/
def IsBlockDiagDomCol (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) : Prop :=
  ∀ j : Fin m,
    ∑ i : Fin m, (if i = j then 0 else blockNorm i j) ≤ invDiagBound j

/-- **Block diagonal dominance by rows** (Higham, 2nd ed., §13.3.1):
    A is block diag dom by rows if Aᵀ is block diag dom by columns. -/
def IsBlockDiagDomRow (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) : Prop :=
  ∀ i : Fin m,
    ∑ j : Fin m, (if i = j then 0 else blockNorm i j) ≤ invDiagBound i

/-- The diagonal-dominance amount `γ_j` in Higham's eq. (13.17), written using
    the scalar block-norm abstraction already used by `IsBlockDiagDomCol`.
    `invDiagBound j` represents `‖A_jj^{-1}‖^{-1}`. -/
noncomputable def blockDiagDomGamma (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) (j : Fin m) : ℝ :=
  invDiagBound j - ∑ i : Fin m, (if i = j then 0 else blockNorm i j)

theorem isBlockDiagDomCol_iff_gamma_nonneg (m : ℕ)
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ) :
    IsBlockDiagDomCol m blockNorm invDiagBound ↔
      ∀ j : Fin m, 0 ≤ blockDiagDomGamma m blockNorm invDiagBound j := by
  constructor
  · intro h j
    unfold blockDiagDomGamma
    linarith [h j]
  · intro h j
    have hj := h j
    unfold blockDiagDomGamma at hj
    linarith

/-- Row-wise diagonal-dominance amount, the transpose analogue of eq. (13.17). -/
noncomputable def blockDiagDomRowGamma (m : ℕ) (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ) (i : Fin m) : ℝ :=
  invDiagBound i - ∑ j : Fin m, (if i = j then 0 else blockNorm i j)

theorem isBlockDiagDomRow_iff_gamma_nonneg (m : ℕ)
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ) :
    IsBlockDiagDomRow m blockNorm invDiagBound ↔
      ∀ i : Fin m, 0 ≤ blockDiagDomRowGamma m blockNorm invDiagBound i := by
  constructor
  · intro h i
    unfold blockDiagDomRowGamma
    linarith [h i]
  · intro h i
    have hi := h i
    unfold blockDiagDomRowGamma at hi
    linarith

/-- The prose definition of row block diagonal dominance is exactly column block
    diagonal dominance of the transposed block-norm table. -/
theorem isBlockDiagDomRow_iff_col_transpose (m : ℕ)
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ) :
    IsBlockDiagDomRow m blockNorm invDiagBound ↔
      IsBlockDiagDomCol m (fun i j => blockNorm j i) invDiagBound := by
  simp [IsBlockDiagDomRow, IsBlockDiagDomCol, eq_comm]

/-- The row-wise dominance amount is the column-wise gamma amount for the
    transposed block-norm table. -/
theorem blockDiagDomRowGamma_eq_colTranspose_gamma (m : ℕ)
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ) (i : Fin m) :
    blockDiagDomRowGamma m blockNorm invDiagBound i =
      blockDiagDomGamma m (fun j i => blockNorm i j) invDiagBound i := by
  simp [blockDiagDomRowGamma, blockDiagDomGamma, eq_comm]

end NumStability
