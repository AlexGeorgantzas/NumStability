-- Quantitative source-facing prose claims from Higham, 2nd ed., Chapter 20.

import NumStability.Algorithms.LeastSquares.Higham20Prose

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-! ## The componentwise condition-number comparison on printed page 385 -/

private theorem higham20_realRectMatrixRank_finiteTranspose
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank (finiteTranspose A) = realRectMatrixRank A := by
  unfold realRectMatrixRank complexMatrixRank
  have hmatrix :
      (realRectToCMatrix (finiteTranspose A) :
          Matrix (Fin n) (Fin m) Complex) =
        Matrix.transpose
          (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex) := by
    ext i j
    rfl
  rw [hmatrix, Matrix.rank_transpose]

private theorem higham20_realRectMatrixRank_le_width
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank A <= n := by
  simpa [realRectMatrixRank, complexMatrixRank] using
    (Matrix.rank_le_width
      (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex))

/-- The page-385 comparison
`cond₂(Aᵀ) <= n * kappa₂(A)`.

Here `Aplus` is the pseudoinverse argument already used by
`higham20Cond2Transpose`; the right-hand side is exactly
`n * ||A||₂ * ||Aplus||₂`.  The proof uses Lemma 6.6 on the two absolute
factors and submultiplicativity of the rectangular operator norm. -/
theorem higham20_cond2Transpose_le_card_mul_kappa2 {m n : Nat}
    (hn : 0 < n) (hnm : n <= m)
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real) :
    higham20Cond2Transpose A Aplus <=
      (n : Real) *
        (complexMatrixOp2 (realRectToCMatrix A) *
          complexMatrixOp2 (realRectToCMatrix Aplus)) := by
  let BT : Fin m -> Fin n -> Real := finiteTranspose Aplus
  let AT : Fin n -> Fin m -> Real := finiteTranspose A
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hBTbase :
      rectOpNorm2Le BT (complexMatrixOp2 (realRectToCMatrix BT)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le BT le_rfl
  have hATbase :
      rectOpNorm2Le AT (complexMatrixOp2 (realRectToCMatrix AT)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le AT le_rfl
  have hBTabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hn BT (complexMatrixOp2_nonneg _) hBTbase
  have hATabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm AT (complexMatrixOp2_nonneg _) hATbase
  have hBTsqrt :
      Real.sqrt (realRectMatrixRank BT : Real) <= Real.sqrt (n : Real) :=
    Real.sqrt_le_sqrt (by
      exact_mod_cast higham20_realRectMatrixRank_le_width BT)
  have hATrank : realRectMatrixRank AT <= n := by
    rw [show AT = finiteTranspose A by rfl,
      higham20_realRectMatrixRank_finiteTranspose]
    exact higham20_realRectMatrixRank_le_width A
  have hATsqrt :
      Real.sqrt (realRectMatrixRank AT : Real) <= Real.sqrt (n : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hATrank)
  have hBTnorm :
      complexMatrixOp2 (realRectToCMatrix BT) =
        complexMatrixOp2 (realRectToCMatrix Aplus) := by
    simpa [BT] using
      complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq Aplus
  have hATnorm :
      complexMatrixOp2 (realRectToCMatrix AT) =
        complexMatrixOp2 (realRectToCMatrix A) := by
    simpa [AT] using
      complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq A
  have hBTabs :
      rectOpNorm2Le (absMatrixRect BT)
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix Aplus)) := by
    apply rectOpNorm2Le_mono _ hBTabs0
    rw [hBTnorm]
    exact mul_le_mul_of_nonneg_right hBTsqrt (complexMatrixOp2_nonneg _)
  have hATabs :
      rectOpNorm2Le (absMatrixRect AT)
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) := by
    apply rectOpNorm2Le_mono _ hATabs0
    rw [hATnorm]
    exact mul_le_mul_of_nonneg_right hATsqrt (complexMatrixOp2_nonneg _)
  have hprod := rectOpNorm2Le_rectMatMul
    (absMatrixRect BT) (absMatrixRect AT)
    (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg _))
    hBTabs hATabs
  have hop :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
      (rectMatMul (absMatrixRect BT) (absMatrixRect AT))
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg _)))
      hprod
  have hmatrix :
      higham20Cond2Transpose A Aplus =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul (absMatrixRect BT) (absMatrixRect AT))) := by
    unfold higham20Cond2Transpose
    congr 1
  rw [hmatrix]
  calc
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul (absMatrixRect BT) (absMatrixRect AT))) <=
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix Aplus)) *
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) := hop
    _ = (n : Real) *
        (complexMatrixOp2 (realRectToCMatrix A) *
          complexMatrixOp2 (realRectToCMatrix Aplus)) := by
      have hsqrt : Real.sqrt (n : Real) * Real.sqrt (n : Real) = (n : Real) :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      calc
        (Real.sqrt (n : Real) *
            complexMatrixOp2 (realRectToCMatrix Aplus)) *
            (Real.sqrt (n : Real) *
              complexMatrixOp2 (realRectToCMatrix A)) =
          (Real.sqrt (n : Real) * Real.sqrt (n : Real)) *
            (complexMatrixOp2 (realRectToCMatrix A) *
              complexMatrixOp2 (realRectToCMatrix Aplus)) := by ring
        _ = _ := by rw [hsqrt]

/-! ## The computable residual substitution following Theorem 20.2 -/

/-- The computable residual `rhat = b - A*y` used immediately after
Theorem 20.2. -/
noncomputable def higham20ComputableResidual {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (y : Fin n -> Real) : Fin m -> Real :=
  lsResidualHigham A b y

/-- The exact source inequality
`|s| <= |rhat| + eps * (f + E|y|)` for
`s = b + Deltab - (A + DeltaA)y`.

Unlike an asymptotic replacement, this is a pointwise finite inequality and
is derived directly from the componentwise perturbation model (20.5). -/
theorem higham20_perturbedResidual_abs_le_computableResidual_add_dataMajorant
    {m n : Nat}
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (y : Fin n -> Real) (eps : Real)
    (hcomp : LSComponentwisePerturbation DeltaA E Deltab f eps) :
    forall i : Fin m,
      |lsResidualHigham (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i) y i| <=
        |higham20ComputableResidual A b y i| +
          eps * lsComponentwiseDataMajorant E f y i := by
  rcases hcomp with ⟨heps, hE, hf, hDeltaA, hDeltab⟩
  intro i
  have hDeltaAy :
      |rectMatMulVec DeltaA y i| <=
        eps * rectMatMulVec E (absVec n y) i := by
    calc
      |rectMatMulVec DeltaA y i| <=
          ∑ j : Fin n, |DeltaA i j * y j| :=
        by
          simpa [rectMatMulVec] using
            (Finset.abs_sum_le_sum_abs
              (fun j : Fin n => DeltaA i j * y j) Finset.univ)
      _ <= ∑ j : Fin n, (eps * E i j) * |y j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hDeltaA i j) (abs_nonneg _)
      _ = eps * rectMatMulVec E (absVec n y) i := by
        unfold rectMatMulVec absVec
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsplit :
      rectMatMulVec (fun i j => A i j + DeltaA i j) y i =
        rectMatMulVec A y i + rectMatMulVec DeltaA y i := by
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [lsResidualHigham, hsplit]
  have hrearrange :
      b i + Deltab i -
          (rectMatMulVec A y i + rectMatMulVec DeltaA y i) =
        (b i - rectMatMulVec A y i) +
          (Deltab i - rectMatMulVec DeltaA y i) := by ring
  rw [hrearrange]
  calc
    |(b i - rectMatMulVec A y i) +
        (Deltab i - rectMatMulVec DeltaA y i)| <=
      |b i - rectMatMulVec A y i| +
        |Deltab i - rectMatMulVec DeltaA y i| := abs_add_le _ _
    _ <= |b i - rectMatMulVec A y i| +
        (|Deltab i| + |rectMatMulVec DeltaA y i|) := by
      exact add_le_add le_rfl (by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (Deltab i) (-rectMatMulVec DeltaA y i)))
    _ <= |b i - rectMatMulVec A y i| +
        (eps * f i + eps * rectMatMulVec E (absVec n y) i) := by
      exact add_le_add le_rfl (add_le_add (hDeltab i) hDeltaAy)
    _ = |higham20ComputableResidual A b y i| +
        eps * lsComponentwiseDataMajorant E f y i := by
      unfold higham20ComputableResidual lsResidualHigham
        lsComponentwiseDataMajorant
      ring

/-! ## The inconsistent-system sufficient condition for `lambda_* < 0` -/

/-- Source-level form of the prose after Theorem 20.5: if the original least
squares problem is inconsistent (`b` is not in the range of `A`) and
`mu != 0`, then `lambda_* < 0`.

The least-squares residual itself is the required left-null vector: normal
equation orthogonality puts it in the left nullspace, while inconsistency makes
its self-pairing nonzero. -/
theorem higham20_lambdaStar_neg_of_b_not_mem_range {m n : Nat}
    (theta : Real) (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real)
    (hmin : IsLeastSquaresMinimizer A b y)
    (hb : b ∉ Set.range (rectMatMulVec A))
    (hmu : lsNormwiseBackwardErrorMu theta y ≠ 0) :
    lsNormwiseBackwardErrorLambdaStar theta A
        (lsResidualHigham A b y) y < 0 := by
  let r := lsResidualHigham A b y
  have hy : y ≠ 0 := by
    intro hy0
    apply hmu
    subst y
    simp [lsNormwiseBackwardErrorMu, vecNorm2Sq]
  have hr : r ≠ 0 := by
    intro hr0
    apply hb
    refine ⟨y, ?_⟩
    ext i
    have hi := congrFun hr0 i
    dsimp [r, lsResidualHigham] at hi
    linarith
  have hleft : forall j : Fin n, (∑ i : Fin (m + 1), A i j * r i) = 0 :=
    hmin.higham_residual_orthogonal rfl
  have hpair : (∑ i : Fin (m + 1), r i * r i) ≠ 0 := by
    have hrnorm : vecNorm2 r ≠ 0 := by
      intro hzero
      apply hr
      funext i
      exact (vecNorm2_eq_zero_iff r).mp hzero i
    have hrsq : vecNorm2Sq r ≠ 0 := by
      rw [← vecNorm2_sq]
      exact pow_ne_zero 2 hrnorm
    simpa [vecNorm2Sq, pow_two] using hrsq
  exact higham20_lambdaStar_neg_of_leftNull_residual_pairing
    theta A r r y hmu hy hleft hpair

end NumStability
