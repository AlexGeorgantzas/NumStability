import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation05.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Lemma02.Symmetrization.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Linearized
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 20 — GeneralRank

Canonical source correspondence module extracted without change from Higham20GeneralWedin.
-/

private noncomputable def higham20GeneralRankCounterexampleA :
    Fin 3 -> Fin 3 -> Real :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]]
private noncomputable def higham20GeneralRankCounterexampleAplus :
    Fin 3 -> Fin 3 -> Real :=
  higham20GeneralRankCounterexampleA
private noncomputable def higham20GeneralRankCounterexampleDeltaA :
    Fin 3 -> Fin 3 -> Real :=
  ![![0, 1 / 20, 0], ![0, 0, 1 / 20], ![0, 0, 0]]
private noncomputable def higham20GeneralRankCounterexampleB :
    Fin 3 -> Fin 3 -> Real :=
  ![![1, 1 / 20, 0], ![0, 1, 1 / 20], ![0, 0, 0]]
private noncomputable def higham20GeneralRankCounterexampleBplus :
    Fin 3 -> Fin 3 -> Real :=
  ![![160400 / 160401, -8000 / 160401, 0],
    ![20 / 160401, 160000 / 160401, 0],
    ![-400 / 160401, 8020 / 160401, 0]]
private noncomputable def higham20GeneralRankCounterexampleb :
    Fin 3 -> Real :=
  ![0, 1, 0]
private noncomputable def higham20GeneralRankCounterexampleDeltab :
    Fin 3 -> Real :=
  ![-1 / 20, 0, 0]
private noncomputable def higham20GeneralRankCounterexamplex :
    Fin 3 -> Real :=
  ![0, 1, 0]
private noncomputable def higham20GeneralRankCounterexampley :
    Fin 3 -> Real :=
  ![-16020 / 160401, 159999 / 160401, 8040 / 160401]
private theorem higham20_general_rank_counterexample_A_moorePenrose :
    RectMoorePenrosePseudoinverse 3 3
      higham20GeneralRankCounterexampleA
      higham20GeneralRankCounterexampleAplus := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleA,
        higham20GeneralRankCounterexampleAplus, rectMatMul,
        Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleA,
        higham20GeneralRankCounterexampleAplus, rectMatMul,
        Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleA,
        higham20GeneralRankCounterexampleAplus, rectMatMul,
        Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleA,
        higham20GeneralRankCounterexampleAplus, rectMatMul,
        Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_B_moorePenrose :
    RectMoorePenrosePseudoinverse 3 3
      higham20GeneralRankCounterexampleB
      higham20GeneralRankCounterexampleBplus := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleB,
        higham20GeneralRankCounterexampleBplus, rectMatMul,
        Fin.sum_univ_succ] <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleB,
        higham20GeneralRankCounterexampleBplus, rectMatMul,
        Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleB,
        higham20GeneralRankCounterexampleBplus, rectMatMul,
        Fin.sum_univ_succ] <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham20GeneralRankCounterexampleB,
        higham20GeneralRankCounterexampleBplus, rectMatMul,
        Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_matrix_perturbation :
    higham20GeneralRankCounterexampleB =
      higham20GeneralRankCounterexampleA +
        higham20GeneralRankCounterexampleDeltaA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham20GeneralRankCounterexampleA,
      higham20GeneralRankCounterexampleB,
      higham20GeneralRankCounterexampleDeltaA]
private theorem higham20_general_rank_counterexample_equal_rank :
    (Matrix.of higham20GeneralRankCounterexampleA).rank =
      (Matrix.of higham20GeneralRankCounterexampleB).rank := by
  have hRange :
      LinearMap.range
          ((Matrix.of higham20GeneralRankCounterexampleA :
            Matrix (Fin 3) (Fin 3) Real).mulVecLin) =
        LinearMap.range
          ((Matrix.of higham20GeneralRankCounterexampleB :
            Matrix (Fin 3) (Fin 3) Real).mulVecLin) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨![z 0 - z 1 / 20, z 1, 0], ?_⟩
      ext i
      fin_cases i <;>
        simp [higham20GeneralRankCounterexampleA,
          higham20GeneralRankCounterexampleB, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
      ring_nf
    · rintro _ ⟨z, rfl⟩
      refine ⟨![z 0 + z 1 / 20, z 1 + z 2 / 20, 0], ?_⟩
      ext i
      fin_cases i <;>
        simp [higham20GeneralRankCounterexampleA,
          higham20GeneralRankCounterexampleB, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] <;> ring
  change Module.finrank Real
      (LinearMap.range
        ((Matrix.of higham20GeneralRankCounterexampleA :
          Matrix (Fin 3) (Fin 3) Real).mulVecLin)) =
    Module.finrank Real
      (LinearMap.range
        ((Matrix.of higham20GeneralRankCounterexampleB :
          Matrix (Fin 3) (Fin 3) Real).mulVecLin))
  rw [hRange]
private theorem higham20_general_rank_counterexample_source_solution :
    rectMatMulVec higham20GeneralRankCounterexampleAplus
        higham20GeneralRankCounterexampleb =
      higham20GeneralRankCounterexamplex := by
  funext i
  fin_cases i <;>
    norm_num [higham20GeneralRankCounterexampleA,
      higham20GeneralRankCounterexampleAplus,
      higham20GeneralRankCounterexampleb,
      higham20GeneralRankCounterexamplex, rectMatMulVec,
      Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_perturbed_solution :
    rectMatMulVec higham20GeneralRankCounterexampleBplus
        (higham20GeneralRankCounterexampleb +
          higham20GeneralRankCounterexampleDeltab) =
      higham20GeneralRankCounterexampley := by
  funext i
  fin_cases i <;>
    norm_num [higham20GeneralRankCounterexampleBplus,
      higham20GeneralRankCounterexampleb,
      higham20GeneralRankCounterexampleDeltab,
      higham20GeneralRankCounterexampley, rectMatMulVec,
      Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_zero_residual :
    higham20GeneralRankCounterexampleb -
        rectMatMulVec higham20GeneralRankCounterexampleA
          higham20GeneralRankCounterexamplex =
      0 := by
  funext i
  fin_cases i <;>
    norm_num [higham20GeneralRankCounterexampleA,
      higham20GeneralRankCounterexampleb,
      higham20GeneralRankCounterexamplex, rectMatMulVec,
      Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_A_rectOpNorm2Le_one :
    rectOpNorm2Le higham20GeneralRankCounterexampleA 1 := by
  intro z
  apply (sq_le_sq₀ (vecNorm2_nonneg _)
    (by simpa using vecNorm2_nonneg z)).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  unfold vecNorm2Sq
  simp only [one_pow, one_mul]
  have haction :
      rectMatMulVec higham20GeneralRankCounterexampleA z =
        (![z 0, z 1, 0] : Fin 3 -> Real) := by
    funext i
    fin_cases i <;>
      simp [higham20GeneralRankCounterexampleA, rectMatMulVec,
        Fin.sum_univ_succ]
  rw [haction]
  simp [Fin.sum_univ_succ]
  exact sq_nonneg (z 2)
private theorem higham20_general_rank_counterexample_DeltaA_rectOpNorm2Le :
    rectOpNorm2Le higham20GeneralRankCounterexampleDeltaA (1 / 20) := by
  intro z
  have hc : (0 : Real) <= 1 / 20 := by norm_num
  apply (sq_le_sq₀ (vecNorm2_nonneg _)
    (mul_nonneg hc (vecNorm2_nonneg z))).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  unfold vecNorm2Sq
  have haction :
      rectMatMulVec higham20GeneralRankCounterexampleDeltaA z =
        (![z 1 / 20, z 2 / 20, 0] : Fin 3 -> Real) := by
    funext i
    fin_cases i <;>
      simp [higham20GeneralRankCounterexampleDeltaA, rectMatMulVec,
        Fin.sum_univ_succ] <;> ring
  rw [haction]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
private theorem higham20_general_rank_counterexample_A_op2_eq_one :
    complexMatrixOp2
        (realRectToCMatrix higham20GeneralRankCounterexampleA) =
      1 := by
  apply le_antisymm
  · exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (by norm_num) higham20_general_rank_counterexample_A_rectOpNorm2Le_one
  · have hcert :=
      rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
        higham20GeneralRankCounterexampleA le_rfl
        (finiteBasisVec (0 : Fin 3))
    have himage :
        rectMatMulVec higham20GeneralRankCounterexampleA
            (finiteBasisVec (0 : Fin 3)) =
          (![1, 0, 0] : Fin 3 -> Real) := by
      funext i
      fin_cases i <;>
        simp [higham20GeneralRankCounterexampleA, rectMatMulVec,
          finiteBasisVec]
    rw [himage, ch7Problem79_vecNorm2_finiteBasisVec] at hcert
    have himageNorm : vecNorm2 (![1, 0, 0] : Fin 3 -> Real) = 1 := by
      unfold vecNorm2 vecNorm2Sq
      norm_num [Fin.sum_univ_succ]
    rw [himageNorm] at hcert
    simpa using hcert
private theorem higham20_general_rank_counterexample_Aplus_op2_eq_one :
    complexMatrixOp2
        (realRectToCMatrix higham20GeneralRankCounterexampleAplus) =
      1 := by
  simpa [higham20GeneralRankCounterexampleAplus] using
    higham20_general_rank_counterexample_A_op2_eq_one
private theorem higham20_general_rank_counterexample_DeltaA_op2_eq :
    complexMatrixOp2
        (realRectToCMatrix higham20GeneralRankCounterexampleDeltaA) =
      1 / 20 := by
  apply le_antisymm
  · exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (by norm_num)
      higham20_general_rank_counterexample_DeltaA_rectOpNorm2Le
  · have hcert :=
      rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
        higham20GeneralRankCounterexampleDeltaA le_rfl
        (finiteBasisVec (1 : Fin 3))
    have himage :
        rectMatMulVec higham20GeneralRankCounterexampleDeltaA
            (finiteBasisVec (1 : Fin 3)) =
          (![1 / 20, 0, 0] : Fin 3 -> Real) := by
      funext i
      fin_cases i <;>
        simp [higham20GeneralRankCounterexampleDeltaA, rectMatMulVec,
          finiteBasisVec]
    rw [himage, ch7Problem79_vecNorm2_finiteBasisVec] at hcert
    have himageNorm :
        vecNorm2 (![1 / 20, 0, 0] : Fin 3 -> Real) = 1 / 20 := by
      unfold vecNorm2 vecNorm2Sq
      rw [show (∑ i : Fin 3,
          (![1 / 20, 0, 0] : Fin 3 -> Real) i ^ 2) =
          (1 / 20 : Real) ^ 2 by norm_num [Fin.sum_univ_succ]]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 20)]
    rw [himageNorm] at hcert
    simpa using hcert
private theorem higham20_general_rank_counterexample_x_norm :
    vecNorm2 higham20GeneralRankCounterexamplex = 1 := by
  unfold vecNorm2 vecNorm2Sq
  norm_num [higham20GeneralRankCounterexamplex, Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_Deltab_norm :
    vecNorm2 higham20GeneralRankCounterexampleDeltab = 1 / 20 := by
  unfold vecNorm2 vecNorm2Sq
  rw [show (∑ i : Fin 3,
      higham20GeneralRankCounterexampleDeltab i ^ 2) =
      (1 / 20 : Real) ^ 2 by
        norm_num [higham20GeneralRankCounterexampleDeltab,
          Fin.sum_univ_succ]]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 20)]
private theorem higham20_general_rank_counterexample_residual_norm :
    vecNorm2
        (higham20GeneralRankCounterexampleb -
          rectMatMulVec higham20GeneralRankCounterexampleA
            higham20GeneralRankCounterexamplex) =
      0 := by
  rw [higham20_general_rank_counterexample_zero_residual]
  unfold vecNorm2 vecNorm2Sq
  simp
private theorem higham20_general_rank_counterexample_solution_difference_sq :
    vecNorm2
        (higham20GeneralRankCounterexampley -
          higham20GeneralRankCounterexamplex) ^ 2 =
      321443604 / 25728480801 := by
  rw [vecNorm2_sq]
  unfold vecNorm2Sq
  norm_num [higham20GeneralRankCounterexampley,
    higham20GeneralRankCounterexamplex, Fin.sum_univ_succ]
private theorem higham20_general_rank_counterexample_strict_violation :
    wedinTheorem20_1SolutionRelativeRHS 1 (1 / 20) 1 1 0 <
      vecNorm2
          (higham20GeneralRankCounterexampley -
            higham20GeneralRankCounterexamplex) /
        vecNorm2 higham20GeneralRankCounterexamplex := by
  rw [higham20_general_rank_counterexample_x_norm, div_one]
  have hRHS :
      wedinTheorem20_1SolutionRelativeRHS 1 (1 / 20) 1 1 0 =
        2 / 19 := by
    unfold wedinTheorem20_1SolutionRelativeRHS
    simp only [mul_zero, zero_div, add_zero, mul_one, one_mul]
    norm_num
  rw [hRHS]
  have hnonneg := vecNorm2_nonneg
    (higham20GeneralRankCounterexampley -
      higham20GeneralRankCounterexamplex)
  have hsq :=
    higham20_general_rank_counterexample_solution_difference_sq
  have hstrict :
      (2 / 19 : Real) ^ 2 < 321443604 / 25728480801 := by
    norm_num
  nlinarith
/-- Source-discrepancy certificate for the sentence on Higham, 2nd ed.,
printed page 402 claiming that Theorem 20.1 holds unchanged under the sole
additional hypothesis `rank B = rank A`.

The witnesses satisfy both Moore--Penrose specifications, equal matrix rank,
the exact perturbation equations, the `eps = 1/20` matrix and data budgets,
and the printed smallness condition.  Their source residual is zero.  The
last conjunct is the strict reverse of equation (20.1), so the literal
unchanged-bound claim cannot be a valid theorem in this generality. -/
theorem higham20_general_rank_unchanged_theorem20_1_source_discrepancy :
    ∃ (A Aplus DeltaA B Bplus : Fin 3 -> Fin 3 -> Real)
      (b Deltab x y : Fin 3 -> Real),
      RectMoorePenrosePseudoinverse 3 3 A Aplus ∧
      RectMoorePenrosePseudoinverse 3 3 B Bplus ∧
      (Matrix.of A).rank = (Matrix.of B).rank ∧
      B = A + DeltaA ∧
      rectMatMulVec Aplus b = x ∧
      rectMatMulVec Bplus (b + Deltab) = y ∧
      b - rectMatMulVec A x = 0 ∧
      complexMatrixOp2 (realRectToCMatrix A) = 1 ∧
      complexMatrixOp2 (realRectToCMatrix Aplus) = 1 ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) = 1 / 20 ∧
      vecNorm2 x = 1 ∧
      vecNorm2 (b - rectMatMulVec A x) = 0 ∧
      vecNorm2 Deltab = 1 / 20 ∧
      complexMatrixOp2 (realRectToCMatrix DeltaA) ≤
        (1 / 20) * complexMatrixOp2 (realRectToCMatrix A) ∧
      vecNorm2 Deltab ≤
        (1 / 20) *
          (complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 x +
            vecNorm2 (b - rectMatMulVec A x)) ∧
      (complexMatrixOp2 (realRectToCMatrix A) *
          complexMatrixOp2 (realRectToCMatrix Aplus)) * (1 / 20) < 1 ∧
      wedinTheorem20_1SolutionRelativeRHS
          (complexMatrixOp2 (realRectToCMatrix A) *
            complexMatrixOp2 (realRectToCMatrix Aplus))
          (1 / 20) (complexMatrixOp2 (realRectToCMatrix A))
          (vecNorm2 x) (vecNorm2 (b - rectMatMulVec A x)) <
        vecNorm2 (y - x) / vecNorm2 x := by
  refine ⟨higham20GeneralRankCounterexampleA,
    higham20GeneralRankCounterexampleAplus,
    higham20GeneralRankCounterexampleDeltaA,
    higham20GeneralRankCounterexampleB,
    higham20GeneralRankCounterexampleBplus,
    higham20GeneralRankCounterexampleb,
    higham20GeneralRankCounterexampleDeltab,
    higham20GeneralRankCounterexamplex,
    higham20GeneralRankCounterexampley,
    higham20_general_rank_counterexample_A_moorePenrose,
    higham20_general_rank_counterexample_B_moorePenrose,
    higham20_general_rank_counterexample_equal_rank,
    higham20_general_rank_counterexample_matrix_perturbation,
    higham20_general_rank_counterexample_source_solution,
    higham20_general_rank_counterexample_perturbed_solution,
    higham20_general_rank_counterexample_zero_residual,
    higham20_general_rank_counterexample_A_op2_eq_one,
    higham20_general_rank_counterexample_Aplus_op2_eq_one,
    higham20_general_rank_counterexample_DeltaA_op2_eq,
    higham20_general_rank_counterexample_x_norm,
    higham20_general_rank_counterexample_residual_norm,
    higham20_general_rank_counterexample_Deltab_norm, ?_, ?_, ?_, ?_⟩
  · rw [higham20_general_rank_counterexample_DeltaA_op2_eq,
      higham20_general_rank_counterexample_A_op2_eq_one]
    norm_num
  · rw [higham20_general_rank_counterexample_Deltab_norm,
      higham20_general_rank_counterexample_A_op2_eq_one,
      higham20_general_rank_counterexample_x_norm,
      higham20_general_rank_counterexample_residual_norm]
    norm_num
  · rw [higham20_general_rank_counterexample_A_op2_eq_one,
      higham20_general_rank_counterexample_Aplus_op2_eq_one]
    norm_num
  · rw [higham20_general_rank_counterexample_A_op2_eq_one,
      higham20_general_rank_counterexample_Aplus_op2_eq_one,
      higham20_general_rank_counterexample_x_norm,
      higham20_general_rank_counterexample_residual_norm]
    have h := higham20_general_rank_counterexample_strict_violation
    rw [higham20_general_rank_counterexample_x_norm, div_one] at h
    simpa only [one_mul, div_one] using h

end NumStability
