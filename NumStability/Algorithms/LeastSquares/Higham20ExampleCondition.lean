-- Exact operator-norm and condition-number comparison for Higham's page-383
-- least-squares perturbation example.

import NumStability.Algorithms.LeastSquares.Higham20Prose
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec

namespace NumStability

open scoped BigOperators

/-- The Moore--Penrose inverse displayed implicitly by the diagonal
`3`-by-`2` matrix in Higham, 2nd ed., Chapter 20, printed page 383. -/
noncomputable def higham20DeltaExampleAplus (delta : Real) :
    Fin 2 -> Fin 3 -> Real :=
  ![![1, 0, 0], ![0, delta⁻¹, 0]]

/-- The explicit table above is the genuine Moore--Penrose pseudoinverse of
the page-383 example matrix whenever `delta` is nonzero. -/
theorem higham20_delta_example_Aplus_moorePenrose {delta : Real}
    (hdelta : delta ≠ 0) :
    RectMoorePenrosePseudoinverse 3 2 (higham20DeltaExampleA delta)
      (higham20DeltaExampleAplus delta) := by
  have hleft :
      rectMatMul (higham20DeltaExampleAplus delta)
          (higham20DeltaExampleA delta) = idMatrix 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [higham20DeltaExampleAplus, higham20DeltaExampleA,
        rectMatMul, idMatrix, Fin.sum_univ_succ, hdelta]
  have hRange :
      IsSymmetricFiniteMatrix
        (rectMatMul (higham20DeltaExampleA delta)
          (higham20DeltaExampleAplus delta)) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [higham20DeltaExampleAplus, higham20DeltaExampleA,
        rectMatMul, Fin.sum_univ_succ, hdelta]
  constructor
  · calc
      rectMatMul
          (rectMatMul (higham20DeltaExampleA delta)
            (higham20DeltaExampleAplus delta))
          (higham20DeltaExampleA delta) =
          rectMatMul (higham20DeltaExampleA delta)
            (rectMatMul (higham20DeltaExampleAplus delta)
              (higham20DeltaExampleA delta)) :=
            rectMatMul_assoc _ _ _
      _ = rectMatMul (higham20DeltaExampleA delta) (idMatrix 2) := by rw [hleft]
      _ = higham20DeltaExampleA delta := rectMatMul_id_right _
  · rw [hleft]
    exact rectMatMul_id_left _
  · exact hRange
  · rw [hleft]
    intro i j
    simp [idMatrix, eq_comm]

private theorem higham20_delta_example_A_rectOpNorm2Le_one
    {delta : Real} (hdelta : delta ≤ 1) (hdelta0 : 0 ≤ delta) :
    rectOpNorm2Le (higham20DeltaExampleA delta) 1 := by
  intro x
  apply (sq_le_sq₀ (vecNorm2_nonneg _)
    (by simpa using vecNorm2_nonneg x)).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  unfold vecNorm2Sq
  simp only [one_pow, one_mul]
  have haction : rectMatMulVec (higham20DeltaExampleA delta) x =
      (![x 0, delta * x 1, 0] : Fin 3 -> Real) := by
    funext i
    fin_cases i <;>
      simp [higham20DeltaExampleA, rectMatMulVec]
  rw [haction]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 1), mul_self_le_mul_self hdelta0 hdelta]

private theorem higham20_delta_example_Aplus_rectOpNorm2Le
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    rectOpNorm2Le (higham20DeltaExampleAplus delta) (1 / delta) := by
  intro x
  have hscale : 0 ≤ 1 / delta := by positivity
  apply (sq_le_sq₀ (vecNorm2_nonneg _) (mul_nonneg hscale (vecNorm2_nonneg _))).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  unfold vecNorm2Sq
  have haction : rectMatMulVec (higham20DeltaExampleAplus delta) x =
      (![x 0, delta⁻¹ * x 1] : Fin 2 -> Real) := by
    funext i
    fin_cases i <;>
      simp [higham20DeltaExampleAplus, rectMatMulVec, Fin.sum_univ_succ]
  rw [haction]
  simp [Fin.sum_univ_succ]
  field_simp [ne_of_gt hdelta]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
    mul_self_le_mul_self hdelta.le hdelta1]

private theorem higham20_delta_example_DeltaA_rectOpNorm2Le
    {delta : Real} (hdelta : 0 ≤ delta) :
    rectOpNorm2Le (higham20DeltaExampleDeltaA delta) (delta / 2) := by
  intro x
  have hc : 0 ≤ delta / 2 := by positivity
  apply (sq_le_sq₀ (vecNorm2_nonneg _) (mul_nonneg hc (vecNorm2_nonneg _))).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  unfold vecNorm2Sq
  have haction : rectMatMulVec (higham20DeltaExampleDeltaA delta) x =
      (![0, 0, delta / 2 * x 1] : Fin 3 -> Real) := by
    funext i
    fin_cases i <;>
      simp [higham20DeltaExampleDeltaA, rectMatMulVec]
  rw [haction]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- Higham, 2nd ed., Chapter 20, printed page 383: in the source regime
`0 < delta ≤ 1`, the example matrix has exact Euclidean operator norm one. -/
theorem higham20_delta_example_A_op2_eq_one {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleA delta)) = 1 := by
  apply le_antisymm
  · exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _ (by norm_num)
      (higham20_delta_example_A_rectOpNorm2Le_one hdelta1 hdelta.le)
  · have hcert :=
        rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          (higham20DeltaExampleA delta) le_rfl (finiteBasisVec (0 : Fin 2))
    have himage :
        rectMatMulVec (higham20DeltaExampleA delta) (finiteBasisVec (0 : Fin 2)) =
          (![1, 0, 0] : Fin 3 -> Real) := by
      funext i
      fin_cases i <;>
        simp [higham20DeltaExampleA, rectMatMulVec, finiteBasisVec]
    rw [himage, ch7Problem79_vecNorm2_finiteBasisVec] at hcert
    have himageNorm : vecNorm2 (![1, 0, 0] : Fin 3 -> Real) = 1 := by
      unfold vecNorm2 vecNorm2Sq
      norm_num [Fin.sum_univ_succ]
    rw [himageNorm] at hcert
    simpa using hcert

/-- Higham, 2nd ed., Chapter 20, printed page 383: the exact Euclidean
operator norm of the example pseudoinverse is `1 / delta`. -/
theorem higham20_delta_example_Aplus_op2_eq_inv {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleAplus delta)) =
      1 / delta := by
  apply le_antisymm
  · exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (by positivity) (higham20_delta_example_Aplus_rectOpNorm2Le hdelta hdelta1)
  · have hcert :=
        rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          (higham20DeltaExampleAplus delta) le_rfl (finiteBasisVec (1 : Fin 3))
    have himage :
        rectMatMulVec (higham20DeltaExampleAplus delta) (finiteBasisVec (1 : Fin 3)) =
          (![0, delta⁻¹] : Fin 2 -> Real) := by
      funext i
      fin_cases i <;>
        simp [higham20DeltaExampleAplus, rectMatMulVec, finiteBasisVec]
    rw [himage, ch7Problem79_vecNorm2_finiteBasisVec] at hcert
    have himageNorm : vecNorm2 (![0, delta⁻¹] : Fin 2 -> Real) = 1 / delta := by
      unfold vecNorm2 vecNorm2Sq
      simp [Fin.sum_univ_succ, abs_of_pos hdelta, Real.sqrt_sq_eq_abs]
    rw [himageNorm] at hcert
    simpa using hcert

/-- Higham, 2nd ed., Chapter 20, printed page 383: the perturbation has
exact Euclidean operator norm `delta / 2`. -/
theorem higham20_delta_example_DeltaA_op2_eq_half {delta : Real}
    (hdelta : 0 < delta) :
    complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleDeltaA delta)) =
      delta / 2 := by
  apply le_antisymm
  · exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (by positivity) (higham20_delta_example_DeltaA_rectOpNorm2Le hdelta.le)
  · have hcert :=
        rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          (higham20DeltaExampleDeltaA delta) le_rfl (finiteBasisVec (1 : Fin 2))
    have himage :
        rectMatMulVec (higham20DeltaExampleDeltaA delta) (finiteBasisVec (1 : Fin 2)) =
          (![0, 0, delta / 2] : Fin 3 -> Real) := by
      funext i
      fin_cases i <;>
        simp [higham20DeltaExampleDeltaA, rectMatMulVec, finiteBasisVec]
    rw [himage, ch7Problem79_vecNorm2_finiteBasisVec] at hcert
    have himageNorm : vecNorm2 (![0, 0, delta / 2] : Fin 3 -> Real) = delta / 2 := by
      unfold vecNorm2 vecNorm2Sq
      rw [show (∑ i : Fin 3, (![0, 0, delta / 2] : Fin 3 -> Real) i ^ 2) =
          (delta / 2) ^ 2 by norm_num [Fin.sum_univ_succ]]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < delta / 2)]
    rw [himageNorm] at hcert
    simpa using hcert

/-- Higham, 2nd ed., Chapter 20, printed page 383: the example has
`kappa_2(A) = 1 / delta`, relative matrix perturbation `delta / 2`, and hence
the two condition-amplified comparison quantities printed after the example. -/
theorem higham20_delta_example_condition_comparison {delta : Real}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    let Aop := complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleA delta))
    let AplusOp :=
      complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleAplus delta))
    let DeltaAop :=
      complexMatrixOp2 (realRectToCMatrix (higham20DeltaExampleDeltaA delta))
    Aop * AplusOp = 1 / delta ∧
      DeltaAop / Aop = delta / 2 ∧
      (Aop * AplusOp) ^ 2 * (DeltaAop / Aop) = 1 / (2 * delta) ∧
      (Aop * AplusOp) * (DeltaAop / Aop) = 1 / 2 := by
  dsimp
  rw [higham20_delta_example_A_op2_eq_one hdelta hdelta1,
    higham20_delta_example_Aplus_op2_eq_inv hdelta hdelta1,
    higham20_delta_example_DeltaA_op2_eq_half hdelta]
  constructor
  · ring
  constructor
  · ring
  constructor
  · field_simp [ne_of_gt hdelta]
  · field_simp [ne_of_gt hdelta]

end NumStability
