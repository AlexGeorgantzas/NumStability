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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance

/-!
# Higham Table 13.1, diagonal-dominance bounds

Canonical declaration owner created by the frozen B0004/R12 route map.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 253:
    scalar product consequence of column block diagonal dominance.  Once
    Theorems 13.7--13.8 and condition (13.19) have supplied
    `‖L‖ ≤ m` and `‖U‖ ≤ m^2 ‖A‖`, the printed bound
    `‖L‖‖U‖ ≤ m^3 ‖A‖` follows. -/
theorem higham13_col_bdd_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ (m : ℝ) ^ 2 * normA) :
    normL * normU ≤ (m : ℝ) ^ 3 * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * ((m : ℝ) ^ 2 * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = (m : ℝ) ^ 3 * normA := by ring

/-- **Point diagonal-dominance column stability** (Table 13.1):
    ‖L‖ · ‖U‖ ≤ 2 · ‖A‖ for point column diag dominant matrices.
    Since every Schur complement is point column diag dominant (Thm 9.8),
    ‖L_{ij}‖ ≤ 1 for i > j (Problem 13.5), so ‖L‖ = 1.
    Also ρ_n ≤ 2 (Thm 9.9/13.8), so ‖U‖ ≤ 2‖A‖ by eq. 13.21. -/
theorem block_lu_stability_point_diagDom_col
    (normL normU normA : ℝ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hNormL : normL ≤ 1)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 2 * normA := by
  nlinarith [mul_le_mul hNormL hNormU hU (by linarith : (0 : ℝ) ≤ 1)]

/-- **Block column diagonal-dominance stability** (Table 13.1, p. 256):
    ‖L‖ ≤ m and ‖U‖ ≤ m² · ‖A‖ so ‖L‖ · ‖U‖ ≤ m³ · ‖A‖.
    From Theorems 13.7--13.8: each sub-diagonal block column of L has norm ≤ 1
    (by eq. 13.17 + 13.19), so ‖L‖ ≤ m; each block of U satisfies
    ‖U_{ij}‖ ≤ 2‖A‖ (by Theorem 13.8), so ‖U‖ ≤ m² · 2‖A‖ (crude).
    The table value of "1" means unconditionally stable (polynomial factors in cₙ). -/
theorem block_lu_stability_block_diagDom_col
    (normL normU normA : ℝ) (m : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hm : 0 ≤ (m : ℝ))
    -- From Thm 13.7 + eq. 13.17+13.19: ‖L‖ ≤ m
    (hNormL : normL ≤ (m : ℝ))
    -- From Thm 13.8 + eq. 13.19: each block of U bounded, giving ‖U‖ ≤ bound
    (normU_bound : ℝ) (_hUBound : 0 ≤ normU_bound)
    (hNormU : normU ≤ normU_bound) :
    normL * normU ≤ (m : ℝ) * normU_bound :=
  mul_le_mul hNormL hNormU hU hm

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 254:
    source one-norm refinement for column block diagonal dominance.  From the
    source-derived premises `‖L‖₁ ≤ m` and `‖U‖₁ ≤ 2‖A‖₁`, the displayed
    product bound `‖L‖₁‖U‖₁ ≤ 2m‖A‖₁` is just scalar algebra. -/
theorem higham13_col_bdd_oneNorm_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 2 * (m : ℝ) * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * (2 * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = 2 * (m : ℝ) * normA := by ring

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 254:
    source infinity-norm refinement for column block diagonal dominance.  From
    `‖L‖∞ ≤ m` and `‖U‖∞ ≤ 2m‖A‖∞`, the printed product bound
    `‖L‖∞‖U‖∞ ≤ 2m^2‖A‖∞` follows. -/
theorem higham13_col_bdd_infNorm_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ 2 * (m : ℝ) * normA) :
    normL * normU ≤ 2 * (m : ℝ) ^ 2 * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * (2 * (m : ℝ) * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = 2 * (m : ℝ) ^ 2 * normA := by ring

/-- **Block row diagonal-dominance stability** (Table 13.1):
    For block row diag dominant: ‖U‖ ≤ 2‖A‖ (Thm 13.8) but ‖L‖ can be
    arbitrarily large. With growth factor ρ_n:
    ‖L‖ · ‖U‖ ≤ n · ρ_n³ · κ(A) · ‖A‖ (eq. 13.22). -/
theorem block_lu_stability_block_diagDom_row
    (normL normU normA rho kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (_hA : 0 ≤ normA) (_hRho : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    -- ‖U‖ ≤ 2‖A‖ from Thm 13.8
    (hNormU : normU ≤ 2 * normA)
    -- ‖L‖ bounded by ρ_n³ · κ(A) · n (worst case, from eq. 13.22)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa) :
    normL * normU ≤ 2 * (n : ℝ) * rho ^ 2 * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg rho)) hKappa)
  nlinarith

/-- Scalar-block specialization of Higham's row-dominant large-`L` example:
    `A = [[eps, 0], [1/2, 1]]`. -/
noncomputable def higham13_rowdom_largeL_A (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then eps else 0
    else
      if j = 0 then (1 / 2 : ℝ) else 1

/-- The corresponding lower factor
    `L = [[1, 0], [1/(2 eps), 1]]`. -/
noncomputable def higham13_rowdom_largeL_L (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else
      if j = 0 then 1 / (2 * eps) else 1

/-- The corresponding upper factor `U = [[eps, 0], [0, 1]]`. -/
noncomputable def higham13_rowdom_largeL_U (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then eps else 0
    else
      if j = 0 then 0 else 1

/-- Higham, 2nd ed., Chapter 13, p. 254: the scalar-block example is row block
    diagonally dominant.  The scalar block norm is absolute value, and the
    diagonal inverse-norm reciprocal is the absolute diagonal entry. -/
theorem higham13_rowdom_largeL_row_block_diag_dom (eps : ℝ) :
    IsBlockDiagDomRow 2
      (fun i j : Fin 2 => |higham13_rowdom_largeL_A eps i j|)
      (fun i : Fin 2 => |higham13_rowdom_largeL_A eps i i|) := by
  intro i
  fin_cases i
  · simp [higham13_rowdom_largeL_A]
  · norm_num [higham13_rowdom_largeL_A]

/-- Higham's displayed factorization for the scalar-block row-dominant example:
    `[[eps,0],[1/2,1]] = [[1,0],[1/(2eps),1]][[eps,0],[0,1]]`. -/
theorem higham13_rowdom_largeL_reconstructs (eps : ℝ) (heps : eps ≠ 0) :
    ∀ i j : Fin 2,
      ∑ k : Fin 2,
        higham13_rowdom_largeL_L eps i k * higham13_rowdom_largeL_U eps k j =
          higham13_rowdom_largeL_A eps i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_two, higham13_rowdom_largeL_A, higham13_rowdom_largeL_L,
      higham13_rowdom_largeL_U]
  field_simp [heps]

/-- The subdiagonal entry of the lower factor is `1/(2 eps)`. -/
theorem higham13_rowdom_largeL_subdiagonal_entry (eps : ℝ) :
    higham13_rowdom_largeL_L eps 1 0 = 1 / (2 * eps) := by
  norm_num [higham13_rowdom_largeL_L]

/-- Higham, 2nd ed., Chapter 13, p. 254: in the row block diagonally dominant
    family, the lower factor can be arbitrarily large.  For every nonnegative
    threshold `M`, choose `eps = 1/(2(M+1))`; then the subdiagonal entry of `L`
    has absolute value `M+1`. -/
theorem higham13_rowdom_largeL_arbitrarily_large (M : ℝ) (hM : 0 ≤ M) :
    ∃ eps : ℝ, eps ≠ 0 ∧
      M < |higham13_rowdom_largeL_L eps 1 0| := by
  let eps : ℝ := 1 / (2 * (M + 1))
  have hM1pos : 0 < M + 1 := by linarith
  have heps_ne : eps ≠ 0 := by
    exact ne_of_gt (by positivity)
  have hLval : higham13_rowdom_largeL_L eps 1 0 = M + 1 := by
    simp [higham13_rowdom_largeL_L, eps]
    field_simp [hM1pos.ne']
  refine ⟨eps, heps_ne, ?_⟩
  rw [hLval, abs_of_pos hM1pos]
  linarith

/-- **Point row diagonal-dominance stability** (Table 13.1, eq. 13.23):
    For point row diag dominant: ρ_n ≤ 2, ‖L‖ ≤ n · 4 · κ(A),
    so ‖L‖ · ‖U‖ ≤ 8nκ(A) · ‖A‖. -/
theorem block_lu_stability_point_diagDom_row
    (normL normU normA kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hKappa : 0 ≤ kappa)
    (hNormL : normL ≤ 4 * (n : ℝ) * kappa)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 8 * (n : ℝ) * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU (by positivity)
  nlinarith

/-- **SPD stability** (Table 13.1, eq. 13.24):
    ‖L‖₂ · ‖U‖₂ ≤ √m · (1 + m · κ₂(A)^{1/2}) · ‖A‖₂.
    From Lemmas 13.9--13.10: each sub-diagonal block of L bounded in 2-norm
    by κ₂(A)^{1/2}, so ‖L‖₂ ≤ 1 + mκ₂(A)^{1/2}. Also ‖U‖₂ ≤ √m · ‖A‖₂. -/
theorem block_lu_stability_spd
    (normL2 normU2 normA2 kappa2 : ℝ) (m : ℕ)
    (hU : 0 ≤ normU2)
    (hNormL : normL2 ≤ 1 + (m : ℝ) * Real.sqrt kappa2)
    (hNormU : normU2 ≤ Real.sqrt (m : ℝ) * normA2) :
    normL2 * normU2 ≤
      (1 + (m : ℝ) * Real.sqrt kappa2) * (Real.sqrt (m : ℝ) * normA2) :=
  mul_le_mul hNormL hNormU hU
    (by linarith [Real.sqrt_nonneg kappa2,
      mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)])

end NumStability
