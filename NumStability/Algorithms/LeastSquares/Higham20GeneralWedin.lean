-- Higham, 2nd ed., Chapter 20, p. 402: constant-rank Wedin algebra.

import NumStability.Algorithms.LeastSquares.Higham20Lemma20_12

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
The full-column proof of (20.1) uses `B⁺B = I`.  For a general
Moore--Penrose inverse this is replaced by Wedin's exact three-term
pseudoinverse-difference decomposition.  This file also isolates the exact
orthogonal splitting of the data term and the domain-null term.  Any sharp
general-rank norm estimate has to act on that combined splitting; applying
the triangle inequality before the squared-norm identity loses information.
-/

/-- Exact data/domain-null decomposition for a pseudoinverse solution.

For every `x` (no rank hypothesis is needed),

`B⁺ A x - x = B⁺ (A-B) x - (I-B⁺B)x`.

The first term is in the range of the domain projection `B⁺B`; the second is
in its orthogonal complement when `Bplus` is the Moore--Penrose inverse. -/
theorem higham20_wedin_solution_data_domain_null_decomposition
    {m n : Nat} (A B : Matrix (Fin m) (Fin n) Real)
    (Bplus : Matrix (Fin n) (Fin m) Real) :
    Bplus * A - 1 =
      Bplus * (A - B) - (1 - Bplus * B) := by
  rw [Matrix.mul_sub]
  abel

/-- The data and domain-null pieces in
`higham20_wedin_solution_data_domain_null_decomposition` are orthogonal.

This is the exact squared-norm aggregation that must be retained in the
general-rank extension of Wedin's solution estimate. -/
theorem higham20_wedin_solution_data_domain_null_vecNorm2Sq
    {m n : Nat} (A B : Matrix (Fin m) (Fin n) Real)
    (Bplus : Matrix (Fin n) (Fin m) Real)
    (hB : RectMoorePenrosePseudoinverse m n B Bplus)
    (x : Fin n -> Real) :
    vecNorm2Sq
        (rectMatMulVec (Bplus * A - 1) x) =
      vecNorm2Sq
          (rectMatMulVec (Bplus * (A - B)) x) +
        vecNorm2Sq
          (rectMatMulVec (1 - Bplus * B) x) := by
  let QB : Matrix (Fin n) (Fin n) Real := Bplus * B
  let IQB : Matrix (Fin n) (Fin n) Real := 1 - QB
  let T : Matrix (Fin n) (Fin n) Real := Bplus * A - 1
  have hB2 : Bplus * B * Bplus = Bplus := by
    simpa [rectMatMul, Matrix.mul_apply] using hB.reproduces_pseudoinverse
  have hQB_sym : IsSymmetricFiniteMatrix QB := by
    intro i j
    simpa [QB, rectMatMul, Matrix.mul_apply] using
      hB.domain_projection_symmetric i j
  have hQB_idem : QB * QB = QB := by
    calc
      QB * QB = (Bplus * B * Bplus) * B := by
        simp only [QB, Matrix.mul_assoc]
      _ = QB := by rw [hB2]
  have hQB_Bplus : QB * Bplus = Bplus := by
    simpa [QB] using hB2
  have hQB_T : QB * T = Bplus * (A - B) := by
    simp only [T, Matrix.mul_sub, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hQB_Bplus]
  have hIQB_Bplus : IQB * Bplus = 0 := by
    rw [show IQB = 1 - QB by rfl, Matrix.sub_mul, Matrix.one_mul,
      hQB_Bplus, sub_self]
  have hIQB_T : IQB * T = -IQB := by
    simp only [T, Matrix.mul_sub, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hIQB_Bplus, Matrix.zero_mul, zero_sub]
  have hpyth :=
    wedinLemma20_12_vecNorm2Sq_rangeProjection_add_complement
      QB hQB_sym hQB_idem
      (rectMatMulVec T x)
  have hQB_T_rect : rectMatMul QB T = Bplus * (A - B) := by
    simpa [rectMatMul, Matrix.mul_apply] using hQB_T
  have hIQB_T_rect : rectMatMul IQB T = -IQB := by
    simpa [rectMatMul, Matrix.mul_apply] using hIQB_T
  have hfirst :
      rectMatMulVec QB (rectMatMulVec T x) =
        rectMatMulVec (Bplus * (A - B)) x := by
    rw [← rectMatMulVec_rectMatMul, hQB_T_rect]
  have hsecond :
      vecNorm2Sq (rectMatMulVec IQB (rectMatMulVec T x)) =
        vecNorm2Sq (rectMatMulVec IQB x) := by
    rw [← rectMatMulVec_rectMatMul, hIQB_T_rect]
    simp [vecNorm2Sq, rectMatMulVec]
  rw [show (fun i j => idMatrix n i j - QB i j) = IQB by
    ext i j
    simp [IQB, idMatrix, Matrix.one_apply]] at hpyth
  rw [hfirst, hsecond] at hpyth
  simpa [QB, IQB, T, rectMatMul, Matrix.mul_apply] using hpyth.symm

/-- Perturbation-sign form of
`higham20_wedin_solution_data_domain_null_vecNorm2Sq`, with `E = B-A` as in
Higham's statement. -/
theorem higham20_wedin_solution_data_domain_null_vecNorm2Sq_sub_rev
    {m n : Nat} (A B : Matrix (Fin m) (Fin n) Real)
    (Bplus : Matrix (Fin n) (Fin m) Real)
    (hB : RectMoorePenrosePseudoinverse m n B Bplus)
    (x : Fin n -> Real) :
    vecNorm2Sq
        (rectMatMulVec (Bplus * A - 1) x) =
      vecNorm2Sq
          (rectMatMulVec (Bplus * (B - A)) x) +
        vecNorm2Sq
          (rectMatMulVec (1 - Bplus * B) x) := by
  rw [higham20_wedin_solution_data_domain_null_vecNorm2Sq A B Bplus hB x]
  have hsign : Bplus * (A - B) = -(Bplus * (B - A)) := by
    rw [Matrix.mul_sub, Matrix.mul_sub]
    abel
  rw [hsign]
  simp [vecNorm2Sq, rectMatMulVec]

/-- The domain-null term is itself a perturbation term.

With `Q_A = A⁺A` and `Q_B = B⁺B`,

`(I-Q_B)Q_A = (I-Q_B)(A-B)ᵀ(A⁺)ᵀ`.

This factorization is the one-sided estimate used below the sharp aggregation:
on vectors fixed by `Q_A`, it bounds the null component by
`||A⁺||₂ ||B-A||₂`. -/
theorem higham20_wedin_domain_null_projection_factorization
    {m n : Nat} (A B : Matrix (Fin m) (Fin n) Real)
    (Aplus Bplus : Matrix (Fin n) (Fin m) Real)
    (hA : RectMoorePenrosePseudoinverse m n A Aplus)
    (hB : RectMoorePenrosePseudoinverse m n B Bplus) :
    (1 - Bplus * B) * (Aplus * A) =
      (1 - Bplus * B) * (A - B).transpose * Aplus.transpose := by
  have hB1 : B * Bplus * B = B := by
    simpa [rectMatMul, Matrix.mul_apply] using hB.reproduces_matrix
  have hQB_sym : (Bplus * B).transpose = Bplus * B := by
    ext i j
    change rectMatMul Bplus B j i = rectMatMul Bplus B i j
    exact (hB.domain_projection_symmetric i j).symm
  have hQA_sym : (Aplus * A).transpose = Aplus * A := by
    ext i j
    change rectMatMul Aplus A j i = rectMatMul Aplus A i j
    exact (hA.domain_projection_symmetric i j).symm
  have hIQB_BT : (1 - Bplus * B) * B.transpose = 0 := by
    have hB_QB : B * (Bplus * B) = B := by
      rw [← Matrix.mul_assoc, hB1]
    have hB_IQB : B * (1 - Bplus * B) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hB_QB, sub_self]
    have ht := congrArg Matrix.transpose hB_IQB
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_zero, hQB_sym] using ht
  have hAt_AplusT : A.transpose * Aplus.transpose = Aplus * A := by
    calc
      A.transpose * Aplus.transpose = (Aplus * A).transpose := by
        rw [Matrix.transpose_mul]
      _ = Aplus * A := hQA_sym
  rw [Matrix.transpose_sub]
  calc
    (1 - Bplus * B) * (Aplus * A) =
        (1 - Bplus * B) * (A.transpose * Aplus.transpose) := by
          rw [hAt_AplusT]
    _ = (1 - Bplus * B) * A.transpose * Aplus.transpose := by
          rw [Matrix.mul_assoc]
    _ = ((1 - Bplus * B) * A.transpose -
          (1 - Bplus * B) * B.transpose) * Aplus.transpose := by
          rw [hIQB_BT, sub_zero]
    _ = (1 - Bplus * B) * (A.transpose - B.transpose) *
          Aplus.transpose := by
          rw [Matrix.mul_sub]

/-- Wedin's exact Moore--Penrose pseudoinverse-difference decomposition.

For `E = B - A`,

`B⁺ - A⁺ = -B⁺ E A⁺
  + B⁺ B⁺ᵀ Eᵀ (I - A A⁺)
  + (I - B⁺ B) Eᵀ A⁺ᵀ A⁺`.

The identity uses only the four Penrose equations for each supplied
pseudoinverse; no rank or norm hypothesis is hidden in the statement. -/
theorem higham20_wedin_pseudoinverse_difference_decomposition
    {m n : Nat} (A B : Matrix (Fin m) (Fin n) Real)
    (Aplus Bplus : Matrix (Fin n) (Fin m) Real)
    (hA : RectMoorePenrosePseudoinverse m n A Aplus)
    (hB : RectMoorePenrosePseudoinverse m n B Bplus) :
    Bplus - Aplus =
      -(Bplus * (B - A) * Aplus) +
        Bplus * Bplus.transpose * (B - A).transpose *
          (1 - A * Aplus) +
        (1 - Bplus * B) * (B - A).transpose * Aplus.transpose * Aplus := by
  have hA1 : A * Aplus * A = A := by
    simpa [rectMatMul, Matrix.mul_apply] using hA.reproduces_matrix
  have hA2 : Aplus * A * Aplus = Aplus := by
    simpa [rectMatMul, Matrix.mul_apply] using hA.reproduces_pseudoinverse
  have hB1 : B * Bplus * B = B := by
    simpa [rectMatMul, Matrix.mul_apply] using hB.reproduces_matrix
  have hB2 : Bplus * B * Bplus = Bplus := by
    simpa [rectMatMul, Matrix.mul_apply] using hB.reproduces_pseudoinverse
  have hPA_sym : (A * Aplus).transpose = A * Aplus := by
    ext i j
    change rectMatMul A Aplus j i = rectMatMul A Aplus i j
    exact (hA.range_projection_symmetric i j).symm
  have hQA_sym : (Aplus * A).transpose = Aplus * A := by
    ext i j
    change rectMatMul Aplus A j i = rectMatMul Aplus A i j
    exact (hA.domain_projection_symmetric i j).symm
  have hPB_sym : (B * Bplus).transpose = B * Bplus := by
    ext i j
    change rectMatMul B Bplus j i = rectMatMul B Bplus i j
    exact (hB.range_projection_symmetric i j).symm
  have hQB_sym : (Bplus * B).transpose = Bplus * B := by
    ext i j
    change rectMatMul Bplus B j i = rectMatMul Bplus B i j
    exact (hB.domain_projection_symmetric i j).symm
  have hBplus_BplusT_BT : Bplus * Bplus.transpose * B.transpose = Bplus := by
    calc
      Bplus * Bplus.transpose * B.transpose =
          Bplus * (Bplus.transpose * B.transpose) := by
            rw [Matrix.mul_assoc]
      _ = Bplus * (B * Bplus).transpose := by
            rw [Matrix.transpose_mul]
      _ = Bplus * (B * Bplus) := by rw [hPB_sym]
      _ = Bplus * B * Bplus := by rw [Matrix.mul_assoc]
      _ = Bplus := hB2
  have hAt_PA : A.transpose * (A * Aplus) = A.transpose := by
    have ht := congrArg Matrix.transpose hA1
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hPA_sym] using ht
  have hAt_IPA : A.transpose * (1 - A * Aplus) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hAt_PA, sub_self]
  have hAt_AplusT_Aplus : A.transpose * Aplus.transpose * Aplus = Aplus := by
    calc
      A.transpose * Aplus.transpose * Aplus =
          (Aplus * A).transpose * Aplus := by rw [Matrix.transpose_mul]
      _ = (Aplus * A) * Aplus := by rw [hQA_sym]
      _ = Aplus := hA2
  have hIQB_BT : (1 - Bplus * B) * B.transpose = 0 := by
    have hB_QB : B * (Bplus * B) = B := by
      rw [← Matrix.mul_assoc, hB1]
    have hB_IQB : B * (1 - Bplus * B) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hB_QB, sub_self]
    have ht := congrArg Matrix.transpose hB_IQB
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_zero, hQB_sym] using ht
  have hfirst :
      -(Bplus * (B - A) * Aplus) =
        -(Bplus * B * Aplus) + Bplus * A * Aplus := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hsecond :
      Bplus * Bplus.transpose * (B - A).transpose *
          (1 - A * Aplus) =
        Bplus * (1 - A * Aplus) := by
    rw [Matrix.transpose_sub]
    calc
      Bplus * Bplus.transpose * (B.transpose - A.transpose) *
            (1 - A * Aplus) =
          (Bplus * Bplus.transpose * B.transpose -
            Bplus * Bplus.transpose * A.transpose) *
              (1 - A * Aplus) := by
                exact congrArg (fun M => M * (1 - A * Aplus))
                  (Matrix.mul_sub (Bplus * Bplus.transpose)
                    B.transpose A.transpose)
      _ = (Bplus * Bplus.transpose * B.transpose) * (1 - A * Aplus) -
            (Bplus * Bplus.transpose * A.transpose) *
              (1 - A * Aplus) := by
                rw [Matrix.sub_mul]
      _ = Bplus * (1 - A * Aplus) -
            Bplus * Bplus.transpose *
              (A.transpose * (1 - A * Aplus)) := by
                rw [hBplus_BplusT_BT]
                simp only [Matrix.mul_assoc]
      _ = Bplus * (1 - A * Aplus) := by
            rw [hAt_IPA, Matrix.mul_zero, sub_zero]
  have hthird :
      (1 - Bplus * B) * (B - A).transpose * Aplus.transpose * Aplus =
        -((1 - Bplus * B) * Aplus) := by
    rw [Matrix.transpose_sub]
    have hzero :
        (1 - Bplus * B) * B.transpose * Aplus.transpose * Aplus = 0 := by
      rw [hIQB_BT, Matrix.zero_mul, Matrix.zero_mul]
    have hcollapse :
        (1 - Bplus * B) * A.transpose * Aplus.transpose * Aplus =
          (1 - Bplus * B) * Aplus := by
      calc
        (1 - Bplus * B) * A.transpose * Aplus.transpose * Aplus =
            (1 - Bplus * B) *
              (A.transpose * Aplus.transpose * Aplus) := by
                simp only [Matrix.mul_assoc]
        _ = (1 - Bplus * B) * Aplus := by rw [hAt_AplusT_Aplus]
    calc
      (1 - Bplus * B) * (B.transpose - A.transpose) *
            Aplus.transpose * Aplus =
          ((1 - Bplus * B) * B.transpose -
            (1 - Bplus * B) * A.transpose) * Aplus.transpose * Aplus := by
              exact congrArg (fun M => M * Aplus.transpose * Aplus)
                (Matrix.mul_sub (1 - Bplus * B) B.transpose A.transpose)
      _ = ((1 - Bplus * B) * B.transpose * Aplus.transpose -
            (1 - Bplus * B) * A.transpose * Aplus.transpose) * Aplus := by
              exact congrArg (fun M => M * Aplus)
                (Matrix.sub_mul ((1 - Bplus * B) * B.transpose)
                  ((1 - Bplus * B) * A.transpose) Aplus.transpose)
      _ = (1 - Bplus * B) * B.transpose * Aplus.transpose * Aplus -
            (1 - Bplus * B) * A.transpose * Aplus.transpose * Aplus := by
              rw [Matrix.sub_mul]
      _ = -((1 - Bplus * B) * Aplus) := by
            rw [hzero, hcollapse, zero_sub]
  rw [hfirst, hsecond, hthird]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  abel

/-!
## Source audit for the general-rank sentence on printed page 402

The sentence following (20.25) says that, when `rank B = rank A`, Theorem
20.1 holds unchanged.  The following exact rational example records that the
literal claim is false for the printed right-hand side of (20.1).  Both
matrices have rank two, both displayed inverse tables satisfy all four
Penrose equations, and the perturbations meet the common `eps = 1/20`
budget.  Nevertheless the relative solution change is strictly larger than
the printed bound.  Keeping this certificate next to the valid Wedin
identities above prevents a false endpoint from being used downstream.
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
