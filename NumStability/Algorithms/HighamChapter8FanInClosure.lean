/-
Algorithms/HighamChapter8FanInClosure.lean

Fresh strict-audit closure for the exact inverse-column-factor part of
Higham (8.13)--(8.20), together with an honesty certificate showing that the
global all-orders envelope cannot itself be rewritten as the printed local
first-order five-factor envelope.
-/
import NumStability.Algorithms.HighamChapter8

namespace NumStability

open scoped BigOperators

/-- A unit lower-triangular order-seven witness for the distinction between
the global absolute fan-in envelope and Higham's local first-order expansion. -/
def higham8_15_rawCubeCounterL : Fin 7 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0],
    ![0, -1, -1, 1, 0, 0, 0],
    ![0, 0, -1, 2, 1, 0, 0],
    ![0, -1, 0, -1, -1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1]]

/-- Exact inverse of `higham8_15_rawCubeCounterL`. -/
def higham8_15_rawCubeCounterLInv : Fin 7 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0],
    ![1, -1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![1, -1, -1, -2, 1, 0, 0],
    ![0, 0, 0, -1, 1, 1, 0],
    ![0, 0, 0, 1, -1, -1, 1]]

/-- Exact inverse of the comparison matrix of the witness. -/
def higham8_15_rawCubeCounterComparisonInv : Fin 7 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0],
    ![2, 2, 1, 1, 0, 0, 0],
    ![5, 5, 3, 2, 1, 0, 0],
    ![8, 8, 4, 3, 1, 1, 0],
    ![8, 8, 4, 3, 1, 1, 1]]

/-- Explicit comparison matrix of the witness. -/
def higham8_15_rawCubeCounterComparison : Fin 7 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0],
    ![0, -1, 1, 0, 0, 0, 0],
    ![0, -1, -1, 1, 0, 0, 0],
    ![0, 0, -1, -2, 1, 0, 0],
    ![0, -1, 0, -1, -1, 1, 0],
    ![0, 0, 0, 0, 0, -1, 1]]

theorem higham8_15_rawCubeCounterL_inverse :
    IsInverse 7 higham8_15_rawCubeCounterL higham8_15_rawCubeCounterLInv := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [higham8_15_rawCubeCounterL, higham8_15_rawCubeCounterLInv,
      Fin.sum_univ_succ] <;> norm_num

theorem higham8_15_rawCubeCounter_comparison_eq :
    comparisonMatrix 7 higham8_15_rawCubeCounterL =
      higham8_15_rawCubeCounterComparison := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comparisonMatrix, higham8_15_rawCubeCounterL,
      higham8_15_rawCubeCounterComparison, Fin.ext_iff]

theorem higham8_15_rawCubeCounterComparison_rightInverse :
    IsRightInverse 7 (comparisonMatrix 7 higham8_15_rawCubeCounterL)
      higham8_15_rawCubeCounterComparisonInv := by
  rw [higham8_15_rawCubeCounter_comparison_eq]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [higham8_15_rawCubeCounterComparison,
      higham8_15_rawCubeCounterComparisonInv, Fin.sum_univ_succ] <;>
    norm_num

theorem higham8_15_rawCubeCounterL_lower :
    ∀ i j : Fin 7, i.val < j.val → higham8_15_rawCubeCounterL i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [higham8_15_rawCubeCounterL] at *

theorem higham8_15_rawCubeCounterL_diag :
    ∀ k : Fin 7, higham8_15_rawCubeCounterL k k ≠ 0 := by
  intro k
  fin_cases k <;> norm_num [higham8_15_rawCubeCounterL]

/-- The actual seven inverse-column-factor absolute product for the witness. -/
noncomputable def higham8_15_rawCubeCounterAbsFan : Fin 7 → Fin 7 → ℝ :=
  higham8_18_fanIn7AbsMatrix 7
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 0)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 1)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 2)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 3)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 4)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 5)
    (higham8_13_lowerColumnInverseFactor 7 higham8_15_rawCubeCounterL 6)

theorem higham8_15_rawCubeCounterAbsFan_eq :
    higham8_15_rawCubeCounterAbsFan =
      higham8_15_rawCubeCounterComparisonInv := by
  exact higham8_18_fanIn7AbsMatrix_eq_comparisonInverse
    higham8_15_rawCubeCounterL higham8_15_rawCubeCounterComparisonInv
    higham8_15_rawCubeCounterL_lower higham8_15_rawCubeCounterL_diag
    higham8_15_rawCubeCounterComparison_rightInverse

/-- Matrix underlying the global raw first-order envelope after substituting
`|b|=|L||x|`. -/
noncomputable def higham8_15_rawCubeCounterRaw : Fin 7 → Fin 7 → ℝ :=
  matMul 7 (absMatrix 7 higham8_15_rawCubeCounterL)
    (matMul 7 higham8_15_rawCubeCounterAbsFan
      (absMatrix 7 higham8_15_rawCubeCounterL))

theorem higham8_15_rawCubeCounterRaw_entry :
    higham8_15_rawCubeCounterRaw 6 0 = 32 := by
  unfold higham8_15_rawCubeCounterRaw
  rw [higham8_15_rawCubeCounterAbsFan_eq]
  (simp [matMul, absMatrix,
    higham8_15_rawCubeCounterL, higham8_15_rawCubeCounterComparisonInv,
    Fin.sum_univ_succ]; norm_num)

theorem higham8_15_rawCubeCounterSourceCube_entry :
    higham8_15_residualCubeBase 7 higham8_15_rawCubeCounterL
        higham8_15_rawCubeCounterLInv 6 0 = 24 := by
  (simp [higham8_15_residualCubeBase, matMul, absMatrix,
    higham8_15_rawCubeCounterL, higham8_15_rawCubeCounterLInv,
    Fin.sum_univ_succ]; norm_num)

/-- **Honesty certificate for the fresh `(8.15)` audit.**  Even when all seven
`M_k` are the literal exact inverses of the source column factors, the global
all-orders absolute envelope cannot be reduced pointwise to the printed
five-factor first-order cube: at entry `(7,1)` the two matrices are `32` and
`24`.  Higham's source does not assert this false reduction; it expands the
local perturbations first and sends their cross terms to `O(u²)`. -/
theorem higham8_15_raw_inverse_factor_envelope_not_le_source_cube :
    ¬ higham8_15_rawCubeCounterRaw 6 0 ≤
      higham8_15_residualCubeBase 7 higham8_15_rawCubeCounterL
        higham8_15_rawCubeCounterLInv 6 0 := by
  rw [higham8_15_rawCubeCounterRaw_entry,
    higham8_15_rawCubeCounterSourceCube_entry]
  norm_num

end NumStability
