import NumStability.Algorithms.LeastSquares.Higham20Lemma20_11
import NumStability.Algorithms.LeastSquares.LSQRSolve

/-!
# Higham Chapter 20: Moore--Penrose source prose

This file records the exact source statements surrounding (20.1): a genuine
rectangular Moore--Penrose inverse sends every right-hand side to the
minimum-2-norm least-squares solution, the full-column-rank inverse has the
Gram formula `(A^T A)^{-1} A^T`, and the rectangular 2-norm condition number
is the ratio of the largest to the least positive singular value.
-/

open scoped BigOperators

namespace NumStability

/-- A least-squares minimizer which has minimum Euclidean norm among all
least-squares minimizers. -/
structure RectMinNormLeastSquaresSolution {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) : Prop where
  isLeastSquaresMinimizer : IsLeastSquaresMinimizer A b x
  min_norm : forall z : Fin n -> Real,
    IsLeastSquaresMinimizer A b z -> vecNorm2 x <= vecNorm2 z

private theorem higham20_rangeProjection_idempotent
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

private theorem higham20_domainProjection_idempotent
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hPenrose2 : rectMatMul (rectMatMul Aplus A) Aplus = Aplus) :
    rectMatMul (rectMatMul Aplus A) (rectMatMul Aplus A) =
      rectMatMul Aplus A := by
  calc
    rectMatMul (rectMatMul Aplus A) (rectMatMul Aplus A) =
        rectMatMul (rectMatMul (rectMatMul Aplus A) Aplus) A := by
          exact (rectMatMul_assoc (rectMatMul Aplus A) Aplus A).symm
    _ = rectMatMul Aplus A := by rw [hPenrose2]

private theorem higham20_vecNorm2Sq_sub_comm
    {n : Nat} (x y : Fin n -> Real) :
    vecNorm2Sq (fun i => x i - y i) =
      vecNorm2Sq (fun i => y i - x i) := by
  unfold vecNorm2Sq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Moore--Penrose fitted vector is the orthogonal projection of `b` onto
the range of `A`, hence `Aplus * b` is an exact least-squares minimizer. -/
theorem higham20_moorePenrose_mulVec_isLeastSquaresMinimizer
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b : Fin m -> Real)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    IsLeastSquaresMinimizer A b (rectMatMulVec Aplus b) := by
  intro y
  let P : Fin m -> Fin m -> Real := rectMatMul A Aplus
  have hIdemEq : rectMatMul P P = P := by
    simpa [P] using
      higham20_rangeProjection_idempotent A Aplus hMP.reproduces_matrix
  have hIdem : forall i j : Fin m,
      finiteMatMul P P i j = P i j := by
    intro i j
    simpa [finiteMatMul, rectMatMul] using
      congrFun (congrFun hIdemEq i) j
  have hfix (z : Fin n -> Real) :
      finiteMatVec P (rectMatMulVec A z) = rectMatMulVec A z := by
    simpa [finiteMatVec, rectMatMulVec] using
      (calc
        rectMatMulVec P (rectMatMulVec A z) =
            rectMatMulVec (rectMatMul P A) z :=
              (rectMatMulVec_rectMatMul P A z).symm
        _ = rectMatMulVec A z := by rw [show rectMatMul P A = A by
          simpa [P] using hMP.reproduces_matrix])
  have hbest :=
    finiteVecNorm2Sq_projection_residual_le_residual_to_range_of_symmetric_idempotent
      P (by simpa [P] using hMP.range_projection_symmetric) hIdem b
      (rectMatMulVec A y)
  rw [hfix y] at hbest
  have hfit :
      rectMatMulVec A (rectMatMulVec Aplus b) = finiteMatVec P b := by
    simpa [P, finiteMatVec, rectMatMulVec] using
      (rectMatMulVec_rectMatMul A Aplus b).symm
  unfold lsObjective lsResidual
  rw [hfit]
  calc
    vecNorm2Sq (fun i => finiteMatVec P b i - b i) =
        vecNorm2Sq (fun i => b i - finiteMatVec P b i) :=
          higham20_vecNorm2Sq_sub_comm (finiteMatVec P b) b
    _ <= vecNorm2Sq (fun i => b i - rectMatMulVec A y i) := by
      simpa [finiteVecNorm2Sq_fin] using hbest
    _ = vecNorm2Sq (fun i => rectMatMulVec A y i - b i) :=
      higham20_vecNorm2Sq_sub_comm b (rectMatMulVec A y)

private theorem higham20_minimizers_have_same_fitted_vector
    {m n : Nat} (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    {x z : Fin n -> Real}
    (hx : IsLeastSquaresMinimizer A b x)
    (hz : IsLeastSquaresMinimizer A b z) :
    rectMatMulVec A z = rectMatMulVec A x := by
  let d : Fin n -> Real := fun j => z j - x j
  have hzx : (fun j => x j + d j) = z := by
    funext j
    simp [d]
  have hobj : lsObjective A b z = lsObjective A b x :=
    le_antisymm (hz x) (hx z)
  have horth :=
    (IsLeastSquaresMinimizer.rectLSNormalEquations hx).residual_orthogonal
  have hcross :
      (Finset.univ.sum fun j : Fin n =>
        d j * (Finset.univ.sum fun i : Fin m =>
          A i j * lsResidual A b x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [horth j]
    ring
  have hexp := lsObjective_add_direction_eq A b x d
  rw [hzx, hobj, hcross] at hexp
  have hAdSq : vecNorm2Sq (rectMatMulVec A d) = 0 := by
    linarith
  have hAdNorm : vecNorm2 (rectMatMulVec A d) = 0 := by
    have hsquare : vecNorm2 (rectMatMulVec A d) ^ 2 = 0 := by
      simpa [vecNorm2_sq] using hAdSq
    nlinarith [vecNorm2_nonneg (rectMatMulVec A d)]
  have hAd : rectMatMulVec A d = 0 := by
    funext i
    exact (vecNorm2_eq_zero_iff (rectMatMulVec A d)).mp hAdNorm i
  rw [show d = fun j => z j - x j by rfl, rectMatMulVec_sub] at hAd
  exact sub_eq_zero.mp hAd

/-- Higham, 2nd ed., Section 20.1: for an arbitrary-rank rectangular matrix,
`A^+ b` is the minimum-2-norm solution among all least-squares minimizers.
The only inverse hypothesis is the four genuine Moore--Penrose equations. -/
theorem higham20_moorePenrose_mulVec_minNormLeastSquares
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b : Fin m -> Real)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    RectMinNormLeastSquaresSolution A b (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  have hx : IsLeastSquaresMinimizer A b x := by
    exact higham20_moorePenrose_mulVec_isLeastSquaresMinimizer A Aplus b hMP
  refine { isLeastSquaresMinimizer := hx, min_norm := ?_ }
  intro z hz
  let Q : Fin n -> Fin n -> Real := rectMatMul Aplus A
  have hIdemEq : rectMatMul Q Q = Q := by
    simpa [Q] using higham20_domainProjection_idempotent A Aplus
      hMP.reproduces_pseudoinverse
  have hIdem : forall i j : Fin n,
      finiteMatMul Q Q i j = Q i j := by
    intro i j
    simpa [finiteMatMul, rectMatMul] using
      congrFun (congrFun hIdemEq i) j
  have hAz : rectMatMulVec A z = rectMatMulVec A x :=
    higham20_minimizers_have_same_fitted_vector A b hx hz
  have hQz : rectMatMulVec Q z = x := by
    calc
      rectMatMulVec Q z = rectMatMulVec Aplus (rectMatMulVec A z) := by
        exact rectMatMulVec_rectMatMul Aplus A z
      _ = rectMatMulVec Aplus (rectMatMulVec A x) := by rw [hAz]
      _ = rectMatMulVec Q x := by
        exact (rectMatMulVec_rectMatMul Aplus A x).symm
      _ = rectMatMulVec Q (rectMatMulVec Aplus b) := rfl
      _ = rectMatMulVec (rectMatMul Q Aplus) b := by
        exact (rectMatMulVec_rectMatMul Q Aplus b).symm
      _ = rectMatMulVec Aplus b := by
        rw [show rectMatMul Q Aplus = Aplus by
          simpa [Q] using hMP.reproduces_pseudoinverse]
      _ = x := rfl
  have hcontract :=
    finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent
      Q (by simpa [Q] using hMP.domain_projection_symmetric) hIdem z
  rw [show finiteMatVec Q z = x by
    simpa [finiteMatVec, rectMatMulVec] using hQz] at hcontract
  simpa [finiteVecNorm2_fin] using hcontract

/-- The full-column-rank Gram formula `(A^T A)^{-1} A^T` is itself the
Moore--Penrose pseudoinverse.  Full column rank is represented by injectivity
of the rectangular matrix action, not by an inverse-shaped assumption. -/
theorem higham20_fullColumn_gramFormula_moorePenrose
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hA : Function.Injective (rectMatMulVec A)) :
    RectMoorePenrosePseudoinverse m n A (lsAplusOfGramNonsingInv A) := by
  let Aplus := lsAplusOfGramNonsingInv A
  have hleft : rectMatMul Aplus A = idMatrix n := by
    simpa [Aplus] using
      (lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric A hA).1
  have hRangeSym : IsSymmetricFiniteMatrix (rectMatMul A Aplus) := by
    simpa [Aplus] using
      (lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric A hA).2
  constructor
  · calc
      rectMatMul (rectMatMul A Aplus) A =
          rectMatMul A (rectMatMul Aplus A) := rectMatMul_assoc A Aplus A
      _ = rectMatMul A (idMatrix n) := by rw [hleft]
      _ = A := rectMatMul_id_right A
  · calc
      rectMatMul (rectMatMul Aplus A) Aplus =
          rectMatMul (idMatrix n) Aplus := by rw [hleft]
      _ = Aplus := rectMatMul_id_left Aplus
  · exact hRangeSym
  · rw [hleft]
    intro i j
    simp [idMatrix, eq_comm]

/-- Entrywise source form of the full-column-rank Gram formula. -/
theorem higham20_fullColumn_gramFormula_entry
    {m n : Nat} (A : Fin m -> Fin n -> Real) (j : Fin n) (i : Fin m) :
    lsAplusOfGramNonsingInv A j i =
      Finset.univ.sum (fun k : Fin n => lsGramNonsingInv A j k * A i k) := by
  rfl

/-- Higham's rectangular condition-number identity on the positive-rank
surface `rank(A) = i+1`:
`||A||_2 ||A^+||_2 = sigma_1(A) / sigma_rank(A)`. -/
theorem higham20_kappa2_moorePenrose_eq_top_div_rankSingular
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (i : Fin n) (hn : 0 < n)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (hrank : complexMatrixRank (realRectToCMatrix A) = i.1 + 1) :
    complexMatrixOp2 (realRectToCMatrix A) *
        complexMatrixOp2 (realRectToCMatrix Aplus) =
      complexMatrixSingularValue (realRectToCMatrix A) ⟨0, hn⟩ /
        complexMatrixSingularValue (realRectToCMatrix A) i := by
  rw [complexMatrixOp2_eq_top_singularValue hn,
    higham20_lemma20_11_pseudoinverse_op2_eq_recip_rankSingular
      A Aplus i hMP hrank]
  simp [div_eq_mul_inv]

end NumStability
