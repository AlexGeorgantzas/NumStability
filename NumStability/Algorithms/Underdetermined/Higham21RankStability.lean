-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Full-row-rank stability under a small pseudoinverse-scaled perturbation.

import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

/-- A right inverse of `A` becomes a left inverse of the transpose action:
    `Aplus^T (A^T y) = y`. -/
theorem higham21_theorem21_1_transpose_left_inverse_of_right_inverse
    {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (y : Fin m -> Real) :
    rectMatMulVec (finiteTranspose Aplus)
        (rectMatMulVec (finiteTranspose A) y) = y := by
  calc
    rectMatMulVec (finiteTranspose Aplus)
        (rectMatMulVec (finiteTranspose A) y) =
        rectMatMulVec (finiteTranspose (rectMatMul A Aplus)) y := by
      exact
        higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
          Aplus A y
    _ = rectMatMulVec (finiteTranspose (idMatrix m)) y := by
      rw [hRight]
    _ = y := by
      ext i
      simp [rectMatMulVec, finiteTranspose, idMatrix]

/-- Higham, 2nd ed., Theorem 21.1, rank-stability factorization:
    `(A + DeltaA)^T y = (I + (Aplus DeltaA)^T) A^T y` whenever
    `A Aplus = I`. -/
theorem higham21_theorem21_1_perturbed_transpose_factorization
    {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (y : Fin m -> Real) :
    rectMatMulVec
        (finiteTranspose (fun i j => A i j + DeltaA i j)) y =
      rectMatMulVec
        (fun i : Fin n => fun j : Fin n =>
          idMatrix n i j +
            finiteTranspose (rectMatMul Aplus DeltaA) i j)
        (rectMatMulVec (finiteTranspose A) y) := by
  let C : Fin n -> Fin n -> Real := rectMatMul Aplus DeltaA
  let z : Fin n -> Real := rectMatMulVec (finiteTranspose A) y
  change
    rectMatMulVec
        (finiteTranspose (fun i j => A i j + DeltaA i j)) y =
      rectMatMulVec
        (fun i : Fin n => fun j : Fin n =>
          idMatrix n i j + finiteTranspose C i j) z
  have hAplusTz :
      rectMatMulVec (finiteTranspose Aplus) z = y := by
    simpa [z] using
      (higham21_theorem21_1_transpose_left_inverse_of_right_inverse
        A Aplus hRight y)
  have hDeltaT :
      rectMatMulVec (finiteTranspose DeltaA) y =
        rectMatMulVec (finiteTranspose C) z := by
    calc
      rectMatMulVec (finiteTranspose DeltaA) y =
          rectMatMulVec (finiteTranspose DeltaA)
            (rectMatMulVec (finiteTranspose Aplus) z) := by
        rw [hAplusTz]
      _ = rectMatMulVec (finiteTranspose C) z := by
        simpa [C] using
          (higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
            DeltaA Aplus z)
  calc
    rectMatMulVec
        (finiteTranspose (fun i j => A i j + DeltaA i j)) y =
        fun j =>
          rectMatMulVec (finiteTranspose A) y j +
            rectMatMulVec (finiteTranspose DeltaA) y j := by
      simpa only [finiteTranspose] using
        (rectMatMulVec_mat_add
          (finiteTranspose A) (finiteTranspose DeltaA) y)
    _ = fun j => z j + rectMatMulVec (finiteTranspose C) z j := by
      rw [hDeltaT]
    _ = rectMatMulVec
          (fun i : Fin n => fun j : Fin n =>
            idMatrix n i j + finiteTranspose C i j) z := by
      symm
      calc
        rectMatMulVec
            (fun i : Fin n => fun j : Fin n =>
              idMatrix n i j + finiteTranspose C i j) z =
            fun j =>
              rectMatMulVec (idMatrix n) z j +
                rectMatMulVec (finiteTranspose C) z j :=
          rectMatMulVec_mat_add (idMatrix n) (finiteTranspose C) z
        _ = fun j => z j + rectMatMulVec (finiteTranspose C) z j := by
          rw [rectMatMulVec_idMatrix]

/-- Higham, 2nd ed., Theorem 21.1, smallness-to-full-rank bridge.
    If `Aplus` is a right pseudoinverse and `||Aplus DeltaA||_2 <= c < 1`,
    then the transpose action of `A + DeltaA` is injective. -/
theorem higham21_theorem21_1_perturbed_transpose_injective_of_right_inverse
    {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real)
    {c : Real}
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hProduct : rectOpNorm2Le (rectMatMul Aplus DeltaA) c)
    (hc : 0 <= c)
    (hc_lt : c < 1) :
    Function.Injective
      (rectMatMulVec
        (finiteTranspose (fun i j => A i j + DeltaA i j))) := by
  let C : Fin n -> Fin n -> Real := rectMatMul Aplus DeltaA
  have hCT : rectOpNorm2Le (finiteTranspose C) c := by
    apply rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le C hc
    simpa [C] using hProduct
  have hIdentityLower : forall z : Fin n -> Real,
      (1 : Real) * vecNorm2 z <=
        vecNorm2 (rectMatMulVec (idMatrix n) z) := by
    intro z
    rw [one_mul, rectMatMulVec_idMatrix]
  have hIplus :
      Function.Injective
        (rectMatMulVec
          (fun i : Fin n => fun j : Fin n =>
            idMatrix n i j + finiteTranspose C i j)) := by
    exact
      rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
        (M := idMatrix n) (Delta := finiteTranspose C)
        (mu := (1 : Real)) (eta := c)
        hIdentityLower hCT hc_lt
  intro y1 y2 hPerturbed
  have hAt :
      rectMatMulVec (finiteTranspose A) y1 =
        rectMatMulVec (finiteTranspose A) y2 := by
    apply hIplus
    calc
      rectMatMulVec
          (fun i : Fin n => fun j : Fin n =>
            idMatrix n i j + finiteTranspose C i j)
          (rectMatMulVec (finiteTranspose A) y1) =
          rectMatMulVec
            (finiteTranspose (fun i j => A i j + DeltaA i j)) y1 := by
        symm
        simpa [C] using
          (higham21_theorem21_1_perturbed_transpose_factorization
            A Aplus DeltaA hRight y1)
      _ = rectMatMulVec
            (finiteTranspose (fun i j => A i j + DeltaA i j)) y2 :=
        hPerturbed
      _ = rectMatMulVec
          (fun i : Fin n => fun j : Fin n =>
            idMatrix n i j + finiteTranspose C i j)
          (rectMatMulVec (finiteTranspose A) y2) := by
        simpa [C] using
          (higham21_theorem21_1_perturbed_transpose_factorization
            A Aplus DeltaA hRight y2)
  calc
    y1 = rectMatMulVec (finiteTranspose Aplus)
        (rectMatMulVec (finiteTranspose A) y1) :=
      (higham21_theorem21_1_transpose_left_inverse_of_right_inverse
        A Aplus hRight y1).symm
    _ = rectMatMulVec (finiteTranspose Aplus)
        (rectMatMulVec (finiteTranspose A) y2) :=
      congrArg (rectMatMulVec (finiteTranspose Aplus)) hAt
    _ = y2 :=
      higham21_theorem21_1_transpose_left_inverse_of_right_inverse
        A Aplus hRight y2

/-- The determinant-facing form of the Theorem 21.1 rank-stability bridge. -/
theorem higham21_theorem21_1_perturbed_gram_det_ne_zero_of_right_inverse
    {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real)
    {c : Real}
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hProduct : rectOpNorm2Le (rectMatMul Aplus DeltaA) c)
    (hc : 0 <= c)
    (hc_lt : c < 1) :
    Not
      (Matrix.det
        (rectGram (fun i j => A i j + DeltaA i j) :
          Matrix (Fin m) (Fin m) Real) = 0) := by
  have hdet :
      Matrix.det
        (rectLSGram
          (finiteTranspose (fun i j => A i j + DeltaA i j)) :
          Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    rectLSGram_det_ne_zero_of_rectMatMulVec_injective
      (finiteTranspose (fun i j => A i j + DeltaA i j))
      (higham21_theorem21_1_perturbed_transpose_injective_of_right_inverse
        A Aplus DeltaA hRight hProduct hc hc_lt)
  simpa [rectLSGram, rectGram, finiteTranspose] using hdet

/-- Canonical determinant-facing wrapper with
    `Aplus = A^T (A A^T)^{-1}`. -/
theorem higham21_theorem21_1_perturbed_gram_det_ne_zero_of_gram_det_ne_zero
    {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    {c : Real}
    (hdetA :
      Not
        (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) DeltaA) c)
    (hc : 0 <= c)
    (hc_lt : c < 1) :
    Not
      (Matrix.det
        (rectGram (fun i j => A i j + DeltaA i j) :
          Matrix (Fin m) (Fin m) Real) = 0) := by
  exact
    higham21_theorem21_1_perturbed_gram_det_ne_zero_of_right_inverse
      A (undetAplusOfGramNonsingInv A) DeltaA
      (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdetA)
      hProduct hc hc_lt

end NumStability
