-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 20, Lemma 20.12 (Wedin's equal-rank projector estimate).

import NumStability.Algorithms.LeastSquares.LSPerturbation
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec

namespace NumStability

open scoped BigOperators

/-- Penrose equation `A Aplus A = A` identifies the range of the range
projection `A Aplus` with the range of `A`; its finite dimension is therefore
the matrix rank of `A`.

This is the rank bridge needed to apply the abstract equal-projection-rank
principal-angle theorem to arbitrary-rank rectangular matrices. -/
theorem higham20_lemma20_12_rangeProjection_finrank_eq_matrixRank
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hPenrose1 : rectMatMul (rectMatMul A Aplus) A = A) :
    Module.finrank Real
        (LinearMap.range
          ((Matrix.of (rectMatMul A Aplus) :
            Matrix (Fin m) (Fin m) Real).mulVecLin)) =
      (Matrix.of A).rank := by
  let AM : Matrix (Fin m) (Fin n) Real := Matrix.of A
  let AplusM : Matrix (Fin n) (Fin m) Real := Matrix.of Aplus
  let PM : Matrix (Fin m) (Fin m) Real := Matrix.of (rectMatMul A Aplus)
  let TA : (Fin n -> Real) →ₗ[Real] (Fin m -> Real) := AM.mulVecLin
  let TAplus : (Fin m -> Real) →ₗ[Real] (Fin n -> Real) := AplusM.mulVecLin
  let TP : (Fin m -> Real) →ₗ[Real] (Fin m -> Real) := PM.mulVecLin
  have hTA_rect (x : Fin n -> Real) : TA x = rectMatMulVec A x := by
    ext i
    simp [TA, AM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTAplus_rect (x : Fin m -> Real) :
      TAplus x = rectMatMulVec Aplus x := by
    ext i
    simp [TAplus, AplusM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTP_rect (x : Fin m -> Real) :
      TP x = rectMatMulVec (rectMatMul A Aplus) x := by
    ext i
    simp [TP, PM, Matrix.mulVec, dotProduct, rectMatMulVec, rectMatMul]
  have hRange : LinearMap.range TP = LinearMap.range TA := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨TAplus x, ?_⟩
      calc
        TA (TAplus x) =
            rectMatMulVec A (rectMatMulVec Aplus x) := by
              rw [hTA_rect, hTAplus_rect]
        _ = rectMatMulVec (rectMatMul A Aplus) x := by
              exact (rectMatMulVec_rectMatMul A Aplus x).symm
        _ = TP x := (hTP_rect x).symm
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      refine ⟨TA z, ?_⟩
      calc
        TP (TA z) =
            rectMatMulVec (rectMatMul A Aplus) (rectMatMulVec A z) := by
              rw [hTP_rect, hTA_rect]
        _ = rectMatMulVec (rectMatMul (rectMatMul A Aplus) A) z := by
              exact
                (rectMatMulVec_rectMatMul (rectMatMul A Aplus) A z).symm
        _ = rectMatMulVec A z := by rw [hPenrose1]
        _ = TA z := (hTA_rect z).symm
  calc
    Module.finrank Real (LinearMap.range TP) =
        Module.finrank Real (LinearMap.range TA) := by rw [hRange]
    _ = AM.rank := by rfl
    _ = (Matrix.of A).rank := by rfl

/-- A Penrose range projection is idempotent. -/
private theorem higham20_lemma20_12_rangeProjection_idempotent
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hPenrose1 : rectMatMul (rectMatMul A Aplus) A = A) :
    rectMatMul (rectMatMul A Aplus) (rectMatMul A Aplus) =
      rectMatMul A Aplus := by
  calc
    rectMatMul (rectMatMul A Aplus) (rectMatMul A Aplus) =
        rectMatMul (rectMatMul (rectMatMul A Aplus) A) Aplus := by
          exact (rectMatMul_assoc (rectMatMul A Aplus) A Aplus).symm
    _ = rectMatMul A Aplus := by rw [hPenrose1]

/-- Higham, 2nd ed., Lemma 20.12: the two cross projections have equal exact
operator `2`-norm when `A` and `B` have equal matrix rank and the supplied
tables are their Moore--Penrose pseudoinverses.

The proof derives equal projection-range dimension from `Matrix.rank A =
Matrix.rank B`; no cross-projection equality is assumed. -/
theorem higham20_lemma20_12_crossProjection_op2_eq_of_equalRank_moorePenrose
    {m n : Nat} (hm : 0 < m)
    (A B : Fin m -> Fin n -> Real)
    (Aplus Bplus : Fin n -> Fin m -> Real)
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hBplus : RectMoorePenrosePseudoinverse m n B Bplus)
    (hRank : (Matrix.of A).rank = (Matrix.of B).rank) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul B Bplus)
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul A Aplus)
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) := by
  let PA : Fin m -> Fin m -> Real := rectMatMul A Aplus
  let PB : Fin m -> Fin m -> Real := rectMatMul B Bplus
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      higham20_lemma20_12_rangeProjection_idempotent
        A Aplus hAplus.reproduces_matrix
  have hIdemB : rectMatMul PB PB = PB := by
    simpa [PB] using
      higham20_lemma20_12_rangeProjection_idempotent
        B Bplus hBplus.reproduces_matrix
  have hRangeFinrank :
      Module.finrank Real
          (LinearMap.range
            ((Matrix.of PB : Matrix (Fin m) (Fin m) Real).mulVecLin)) =
        Module.finrank Real
          (LinearMap.range
            ((Matrix.of PA : Matrix (Fin m) (Fin m) Real).mulVecLin)) := by
    calc
      Module.finrank Real
          (LinearMap.range
            ((Matrix.of PB : Matrix (Fin m) (Fin m) Real).mulVecLin)) =
          (Matrix.of B).rank := by
            simpa [PB] using
              higham20_lemma20_12_rangeProjection_finrank_eq_matrixRank
                B Bplus hBplus.reproduces_matrix
      _ = (Matrix.of A).rank := hRank.symm
      _ = Module.finrank Real
          (LinearMap.range
            ((Matrix.of PA : Matrix (Fin m) (Fin m) Real).mulVecLin)) := by
            simpa [PA] using
              (higham20_lemma20_12_rangeProjection_finrank_eq_matrixRank
                A Aplus hAplus.reproduces_matrix).symm
  simpa [PA, PB] using
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_range_finrank_eq
      hm PB PA
      (by simpa [PB] using hBplus.range_projection_symmetric)
      (by simpa [PA] using hAplus.range_projection_symmetric)
      hIdemB hIdemA hRangeFinrank

/-- The complement of a finite symmetric idempotent projection is
nonexpansive in the Euclidean norm. -/
private theorem higham20_lemma20_12_projectionComplement_rectOpNorm2Le_one
    {m : Nat} (P : Fin m -> Fin m -> Real)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : rectMatMul P P = P) :
    rectOpNorm2Le (fun i j => idMatrix m i j - P i j) 1 := by
  intro x
  have hdecomp :=
    wedinLemma20_12_vecNorm2Sq_rangeProjection_add_complement
      P hSym hIdem x
  have hsq :
      vecNorm2
          (rectMatMulVec (fun i j => idMatrix m i j - P i j) x) ^ 2 <=
        vecNorm2 x ^ 2 := by
    rw [vecNorm2_sq, vecNorm2_sq]
    nlinarith [vecNorm2Sq_nonneg (rectMatMulVec P x)]
  have hle :
      vecNorm2 (rectMatMulVec (fun i j => idMatrix m i j - P i j) x) <=
        vecNorm2 x :=
    (sq_le_sq₀
      (vecNorm2_nonneg
        (rectMatMulVec (fun i j => idMatrix m i j - P i j) x))
      (vecNorm2_nonneg x)).mp hsq
  simpa using hle

/-- The elementary one-sided part of Lemma 20.12 for an arbitrary-rank
Moore--Penrose range projection. -/
private theorem higham20_lemma20_12_complement_mul_rangeProjection_bound
    {m n : Nat} (A B : Fin m -> Fin n -> Real)
    (Aplus Bplus : Fin n -> Fin m -> Real)
    {delta BplusNorm : Real}
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hDeltaNonneg : 0 <= delta)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplusNorm : rectOpNorm2Le Bplus BplusNorm) :
    rectOpNorm2Le
      (rectMatMul
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
        (rectMatMul B Bplus))
      (delta * BplusNorm) := by
  let PA : Fin m -> Fin m -> Real := rectMatMul A Aplus
  let IPA : Fin m -> Fin m -> Real := fun i j => idMatrix m i j - PA i j
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      higham20_lemma20_12_rangeProjection_idempotent
        A Aplus hAplus.reproduces_matrix
  have hIPA : rectOpNorm2Le IPA 1 :=
    higham20_lemma20_12_projectionComplement_rectOpNorm2Le_one
      PA (by simpa [PA] using hAplus.range_projection_symmetric) hIdemA
  have hIPA_A_zero (z : Fin n -> Real) :
      rectMatMulVec IPA (rectMatMulVec A z) = 0 := by
    have hfix :
        rectMatMulVec PA (rectMatMulVec A z) = rectMatMulVec A z := by
      calc
        rectMatMulVec PA (rectMatMulVec A z) =
            rectMatMulVec (rectMatMul PA A) z := by
              exact (rectMatMulVec_rectMatMul PA A z).symm
        _ = rectMatMulVec A z := by
              simpa [PA] using congrArg (fun M => rectMatMulVec M z)
                hAplus.reproduces_matrix
    rw [show IPA = (fun i j => idMatrix m i j - PA i j) by rfl,
      wedinLemma20_12_rectMatMulVec_projectionComplement, hfix]
    ext i
    simp
  intro y
  let z : Fin n -> Real := rectMatMulVec Bplus y
  have hB_decomp :
      rectMatMulVec B z =
        fun i => rectMatMulVec (fun i j => B i j - A i j) z i +
          rectMatMulVec A z i := by
    ext i
    unfold rectMatMulVec
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hvec :
      rectMatMulVec
          (rectMatMul IPA (rectMatMul B Bplus)) y =
        rectMatMulVec IPA
          (rectMatMulVec (fun i j => B i j - A i j) z) := by
    calc
      rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y =
          rectMatMulVec IPA (rectMatMulVec (rectMatMul B Bplus) y) := by
            rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA (rectMatMulVec B z) := by
            rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA
          (fun i => rectMatMulVec (fun i j => B i j - A i j) z i +
            rectMatMulVec A z i) := by rw [hB_decomp]
      _ = fun i =>
          rectMatMulVec IPA
              (rectMatMulVec (fun i j => B i j - A i j) z) i +
            rectMatMulVec IPA (rectMatMulVec A z) i := by
              rw [rectMatMulVec_add]
      _ = rectMatMulVec IPA
          (rectMatMulVec (fun i j => B i j - A i j) z) := by
            rw [hIPA_A_zero z]
            ext i
            simp
  calc
    vecNorm2
        (rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y) =
      vecNorm2
        (rectMatMulVec IPA
          (rectMatMulVec (fun i j => B i j - A i j) z)) := by rw [hvec]
    _ <= vecNorm2 (rectMatMulVec (fun i j => B i j - A i j) z) := by
      simpa using hIPA (rectMatMulVec (fun i j => B i j - A i j) z)
    _ <= delta * vecNorm2 z := hDelta z
    _ <= delta * (BplusNorm * vecNorm2 y) :=
      mul_le_mul_of_nonneg_left (hBplusNorm y) hDeltaNonneg
    _ = (delta * BplusNorm) * vecNorm2 y := by ring

/-- The source orientation `P_B (I-P_A)` of the elementary one-sided bound. -/
private theorem higham20_lemma20_12_rangeProjection_mul_complement_bound
    {m n : Nat} (A B : Fin m -> Fin n -> Real)
    (Aplus Bplus : Fin n -> Fin m -> Real)
    {delta BplusNorm : Real}
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hBplus : RectMoorePenrosePseudoinverse m n B Bplus)
    (hDeltaNonneg : 0 <= delta)
    (hBplusNormNonneg : 0 <= BplusNorm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplusNorm : rectOpNorm2Le Bplus BplusNorm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * BplusNorm) := by
  let PB : Fin m -> Fin m -> Real := rectMatMul B Bplus
  let IPA : Fin m -> Fin m -> Real :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  have hhalf : rectOpNorm2Le (rectMatMul IPA PB) (delta * BplusNorm) := by
    simpa [PB, IPA] using
      higham20_lemma20_12_complement_mul_rangeProjection_bound
        A B Aplus Bplus hAplus hDeltaNonneg hDelta hBplusNorm
  have htrans :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul IPA PB)
      (mul_nonneg hDeltaNonneg hBplusNormNonneg) hhalf
  have hIPA_sym : IsSymmetricFiniteMatrix IPA := by
    simpa [IPA] using
      wedinLemma20_12_projectionComplement_symmetric
        (rectMatMul A Aplus) hAplus.range_projection_symmetric
  have htranspose : finiteTranspose (rectMatMul IPA PB) = rectMatMul PB IPA :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IPA PB hIPA_sym (by simpa [PB] using hBplus.range_projection_symmetric)
  rw [htranspose] at htrans
  simpa [PB, IPA] using htrans

/-- Higham, 2nd ed., Lemma 20.12 in exact source norm form for arbitrary-rank
real `m`-by-`n` matrices.

The result states both the printed equality
`||P_B(I-P_A)||_2 = ||P_A(I-P_B)||_2` and its printed upper bound
`||B-A||_2 * min (||Aplus||_2) (||Bplus||_2)`. -/
theorem higham20_lemma20_12_equalRank_moorePenrose_of_pos
    {m n : Nat} (hm : 0 < m)
    (A B : Fin m -> Fin n -> Real)
    (Aplus Bplus : Fin n -> Fin m -> Real)
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hBplus : RectMoorePenrosePseudoinverse m n B Bplus)
    (hRank : (Matrix.of A).rank = (Matrix.of B).rank) :
    let PBIPA :=
      rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
    let PAIPB :=
      rectMatMul
        (rectMatMul A Aplus)
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
    let Delta := fun i j => B i j - A i j
    complexMatrixOp2 (realRectToCMatrix PBIPA) =
        complexMatrixOp2 (realRectToCMatrix PAIPB) /\
      complexMatrixOp2 (realRectToCMatrix PBIPA) <=
        complexMatrixOp2 (realRectToCMatrix Delta) *
          min (complexMatrixOp2 (realRectToCMatrix Aplus))
            (complexMatrixOp2 (realRectToCMatrix Bplus)) := by
  dsimp only
  let delta : Real :=
    complexMatrixOp2 (realRectToCMatrix (fun i j => B i j - A i j))
  let AplusNorm : Real := complexMatrixOp2 (realRectToCMatrix Aplus)
  let BplusNorm : Real := complexMatrixOp2 (realRectToCMatrix Bplus)
  have hDeltaNonneg : 0 <= delta := by
    exact complexMatrixOp2_nonneg _
  have hAplusNormNonneg : 0 <= AplusNorm := by
    exact complexMatrixOp2_nonneg _
  have hBplusNormNonneg : 0 <= BplusNorm := by
    exact complexMatrixOp2_nonneg _
  have hDelta :
      rectOpNorm2Le (fun i j => B i j - A i j) delta :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hAplusBound : rectOpNorm2Le Aplus AplusNorm :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hBplusBound : rectOpNorm2Le Bplus BplusNorm :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hEq :=
    higham20_lemma20_12_crossProjection_op2_eq_of_equalRank_moorePenrose
      hm A B Aplus Bplus hAplus hBplus hRank
  have hPBIPA_Bplus :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * BplusNorm) :=
    higham20_lemma20_12_rangeProjection_mul_complement_bound
      A B Aplus Bplus hAplus hBplus hDeltaNonneg hBplusNormNonneg
      hDelta hBplusBound
  have hPAIPB_Aplus :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul A Aplus)
          (fun i j => idMatrix m i j - rectMatMul B Bplus i j))
        (delta * AplusNorm) :=
    higham20_lemma20_12_rangeProjection_mul_complement_bound
      B A Bplus Aplus hBplus hAplus hDeltaNonneg hAplusNormNonneg
      (wedinLemma20_12_rectOpNorm2Le_sub_rev A B hDelta) hAplusBound
  have hPBIPA_le_Bplus :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) <=
        delta * BplusNorm :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (mul_nonneg hDeltaNonneg hBplusNormNonneg) hPBIPA_Bplus
  have hPAIPB_le_Aplus :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) <=
        delta * AplusNorm :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (mul_nonneg hDeltaNonneg hAplusNormNonneg) hPAIPB_Aplus
  have hPBIPA_le_Aplus :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) <=
        delta * AplusNorm := by
    rw [hEq]
    exact hPAIPB_le_Aplus
  refine ⟨hEq, ?_⟩
  by_cases hAB : AplusNorm <= BplusNorm
  · simpa [delta, AplusNorm, BplusNorm, min_eq_left hAB] using hPBIPA_le_Aplus
  · have hBA : BplusNorm <= AplusNorm := le_of_not_ge hAB
    simpa [delta, AplusNorm, BplusNorm, min_eq_right hBA] using hPBIPA_le_Bplus

/-- Higham, 2nd ed., Lemma 20.12 for arbitrary natural matrix dimensions.

The zero-row case is vacuous (both cross projections have exact norm zero);
the positive-row case is the principal-angle proof above. Thus this endpoint
has exactly the source mathematical hypotheses: two Moore--Penrose
pseudoinverses and equality of the two matrix ranks. -/
theorem higham20_lemma20_12_equalRank_moorePenrose
    {m n : Nat} (A B : Fin m -> Fin n -> Real)
    (Aplus Bplus : Fin n -> Fin m -> Real)
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hBplus : RectMoorePenrosePseudoinverse m n B Bplus)
    (hRank : (Matrix.of A).rank = (Matrix.of B).rank) :
    let PBIPA :=
      rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
    let PAIPB :=
      rectMatMul
        (rectMatMul A Aplus)
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
    let Delta := fun i j => B i j - A i j
    complexMatrixOp2 (realRectToCMatrix PBIPA) =
        complexMatrixOp2 (realRectToCMatrix PAIPB) /\
      complexMatrixOp2 (realRectToCMatrix PBIPA) <=
        complexMatrixOp2 (realRectToCMatrix Delta) *
          min (complexMatrixOp2 (realRectToCMatrix Aplus))
            (complexMatrixOp2 (realRectToCMatrix Bplus)) := by
  cases m with
  | zero =>
      simp [rectMatMul, complexMatrixOp2]
  | succ m =>
      exact higham20_lemma20_12_equalRank_moorePenrose_of_pos
        (Nat.succ_pos m) A B Aplus Bplus hAplus hBplus hRank

end NumStability
