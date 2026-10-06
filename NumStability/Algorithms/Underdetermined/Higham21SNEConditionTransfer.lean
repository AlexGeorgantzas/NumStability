-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Fixed-radius transfer of the SNE componentwise condition expression.

import NumStability.Algorithms.Underdetermined.Higham21PerturbationRadius

namespace NumStability

open scoped BigOperators

/-!
# Fixed-radius SNE condition transfer

This file records the honest local transfer needed after the nearby-system
analysis.  Write `B(theta) = A + theta D`.  A radius-independent envelope
`beta` for the perturbed Gram inverses makes the exact inverse-difference
identity from (21.7) uniform on `0 <= theta <= rho`.  Consequently both the
pseudoinverse and

`cond2(B(theta)) * ||B(theta)^+ b||_2`

differ from their base values by at most `theta` times explicit coefficients.
No hypothesis equivalent to the desired condition transfer is assumed.
-/

/-- Radius-uniform coefficient for the pseudoinverse difference
`B(theta)^+ - A^+`. -/
noncomputable def higham21SNEPseudoinverseDifferenceCoefficient
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G : Fin m -> Fin m -> Real) (rho beta : Real) : Real :=
  frobNormRect D * beta +
    frobNormRect A *
      higham21Eq21_7InverseDifferenceCoefficient A D G rho beta

/-- Radius-uniform coefficient for transferring `cond2(B(theta))` back to
`cond2(A)`. -/
noncomputable def higham21SNEConditionDifferenceCoefficient
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G : Fin m -> Fin m -> Real) (rho beta : Real) : Real :=
  let Aplus := undetAplusOfGramInv A G
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  frobNormRect Aplus * frobNormRect D +
    pC * frobNormRect A + rho * pC * frobNormRect D

/-- The full fixed-radius coefficient for transferring the product of the
componentwise condition number and the exact minimum-norm solution norm. -/
noncomputable def higham21SNEConditionTransferCoefficient
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (G : Fin m -> Fin m -> Real)
    (rho beta : Real) : Real :=
  let Aplus := undetAplusOfGramInv A G
  let x := rectMatMulVec Aplus b
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  let cC := higham21SNEConditionDifferenceCoefficient A D G rho beta
  cC * vecNorm2 x +
    higham21Cond2With A Aplus * (pC * vecNorm2 b) +
      rho * cC * (pC * vecNorm2 b)

/-- The fixed-radius inverse-difference coefficient is nonnegative whenever
the radius and inverse envelope are nonnegative. -/
theorem higham21_sne_inverseDifferenceCoefficient_nonneg
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G : Fin m -> Fin m -> Real) (rho beta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) :
    0 <= higham21Eq21_7InverseDifferenceCoefficient A D G rho beta := by
  dsimp [higham21Eq21_7InverseDifferenceCoefficient,
    higham21Eq21_7InverseQuadraticCoefficient]
  exact add_nonneg
    (add_nonneg (frobNorm_nonneg _)
      (mul_nonneg hrho (frobNorm_nonneg _)))
    (mul_nonneg hrho (mul_nonneg (sq_nonneg _) hbeta))

/-- The induced fixed-radius pseudoinverse-difference coefficient is
nonnegative. -/
theorem higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G : Fin m -> Fin m -> Real) (rho beta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) :
    0 <= higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta := by
  unfold higham21SNEPseudoinverseDifferenceCoefficient
  exact add_nonneg
    (mul_nonneg (frobNormRect_nonneg D) hbeta)
    (mul_nonneg (frobNormRect_nonneg A)
      (higham21_sne_inverseDifferenceCoefficient_nonneg
        A D G rho beta hrho hbeta))

/-- The fixed-radius componentwise-condition transfer coefficient is
nonnegative. -/
theorem higham21_sne_conditionDifferenceCoefficient_nonneg
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G : Fin m -> Fin m -> Real) (rho beta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) :
    0 <= higham21SNEConditionDifferenceCoefficient A D G rho beta := by
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  have hpC : 0 <= pC := by
    exact higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  dsimp [higham21SNEConditionDifferenceCoefficient]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (frobNormRect_nonneg _) (frobNormRect_nonneg D))
      (mul_nonneg hpC (frobNormRect_nonneg A)))
    (mul_nonneg (mul_nonneg hrho hpC) (frobNormRect_nonneg D))

/-- The full fixed-radius condition-times-solution transfer coefficient is
nonnegative. -/
theorem higham21_sne_conditionTransferCoefficient_nonneg
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (G : Fin m -> Fin m -> Real)
    (rho beta : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta) :
    0 <= higham21SNEConditionTransferCoefficient A D b G rho beta := by
  let Aplus := undetAplusOfGramInv A G
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  let cC := higham21SNEConditionDifferenceCoefficient A D G rho beta
  have hpC : 0 <= pC :=
    higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  have hcC : 0 <= cC :=
    higham21_sne_conditionDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  simp only [higham21SNEConditionTransferCoefficient]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hcC (vecNorm2_nonneg _))
      (mul_nonneg (higham21Cond2With_nonneg A Aplus)
        (mul_nonneg hpC (vecNorm2_nonneg b))))
    (mul_nonneg (mul_nonneg hrho hcC)
      (mul_nonneg hpC (vecNorm2_nonneg b)))

/-- The exact (21.7) inverse identity gives a linear, radius-uniform
Frobenius bound for the corresponding pseudoinverses. -/
theorem higham21_sne_pseudoinverse_difference_frobNorm_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    frobNormRect
        (fun j i =>
          undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta j i -
            undetAplusOfGramInv A G j i) <=
      theta * higham21SNEPseudoinverseDifferenceCoefficient
        A D G rho beta := by
  let dG : Fin m -> Fin m -> Real := fun i r => Gtheta i r - G i r
  let invC := higham21Eq21_7InverseDifferenceCoefficient A D G rho beta
  have habs_theta : |theta| = theta := abs_of_nonneg htheta
  have hGtheta_norm_rect : frobNormRect Gtheta <= beta := by
    simpa [frobNormRect_eq_frobNormFn] using hGtheta_norm
  have hdG_eq :
      dG = higham21Eq21_7GramInverseDifferenceModel G
        (higham21Eq21_7GramPerturbation A D theta) Gtheta := by
    ext i r
    exact higham21Eq21_7_gramInverse_difference
      A D G Gtheta theta hG.1 hGtheta.2 i r
  have hdG_norm : frobNormRect dG <= theta * invC := by
    rw [hdG_eq, frobNormRect_eq_frobNormFn]
    simpa [habs_theta, invC] using
      higham21Eq21_7_inverseDifference_frobNorm_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta
        (by simpa [habs_theta] using htheta_rho) hGtheta_norm
  have hdecomp :
      (fun j i =>
          undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta j i -
            undetAplusOfGramInv A G j i) =
        fun j i =>
          theta * rectMatMul (finiteTranspose D) Gtheta j i +
            rectMatMul (finiteTranspose A) dG j i := by
    ext j i
    simp only [undetAplusOfGramInv, higham21Eq21_7ScaledMatrix,
      rectMatMul, finiteTranspose, dG]
    simp_rw [add_mul, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  rw [hdecomp]
  calc
    frobNormRect
        (fun j i =>
          theta * rectMatMul (finiteTranspose D) Gtheta j i +
            rectMatMul (finiteTranspose A) dG j i) <=
      frobNormRect
          (fun j i => theta * rectMatMul (finiteTranspose D) Gtheta j i) +
        frobNormRect (rectMatMul (finiteTranspose A) dG) :=
      frobNormRect_add_le _ _
    _ = theta * frobNormRect (rectMatMul (finiteTranspose D) Gtheta) +
        frobNormRect (rectMatMul (finiteTranspose A) dG) := by
      rw [frobNormRect_smul, habs_theta]
    _ <= theta * (frobNormRect (finiteTranspose D) * frobNormRect Gtheta) +
        frobNormRect (finiteTranspose A) * frobNormRect dG := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (frobNormRect_rectMatMul_le (finiteTranspose D) Gtheta) htheta)
        (frobNormRect_rectMatMul_le (finiteTranspose A) dG)
    _ <= theta * (frobNormRect D * beta) +
        frobNormRect A * (theta * invC) := by
      rw [frobNormRect_finiteTranspose, frobNormRect_finiteTranspose]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGtheta_norm_rect
            (frobNormRect_nonneg D)) htheta)
        (mul_le_mul_of_nonneg_left hdG_norm (frobNormRect_nonneg A))
    _ = theta * higham21SNEPseudoinverseDifferenceCoefficient
          A D G rho beta := by
      simp only [higham21SNEPseudoinverseDifferenceCoefficient, invC]
      ring

/-- The exact nearby dual vector `G(theta) b` differs from `G b` by a
linear-in-`theta` amount on the fixed radius.  This is the direct-source
closure consequence of the (21.7) inverse-difference identity. -/
theorem higham21_sne_dual_solution_difference_vecNorm2_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    vecNorm2
        (fun i => matMulVec m Gtheta b i - matMulVec m G b i) <=
      theta *
        (higham21Eq21_7InverseDifferenceCoefficient A D G rho beta *
          vecNorm2 b) := by
  let dG : Fin m -> Fin m -> Real := fun i r => Gtheta i r - G i r
  let invC := higham21Eq21_7InverseDifferenceCoefficient A D G rho beta
  have habs_theta : |theta| = theta := abs_of_nonneg htheta
  have hdG_eq :
      dG = higham21Eq21_7GramInverseDifferenceModel G
        (higham21Eq21_7GramPerturbation A D theta) Gtheta := by
    ext i r
    exact higham21Eq21_7_gramInverse_difference
      A D G Gtheta theta hG.1 hGtheta.2 i r
  have hdG_norm : frobNormRect dG <= theta * invC := by
    rw [hdG_eq, frobNormRect_eq_frobNormFn]
    simpa [habs_theta, invC] using
      higham21Eq21_7_inverseDifference_frobNorm_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta
        (by simpa [habs_theta] using htheta_rho) hGtheta_norm
  have haction :
      (fun i => matMulVec m Gtheta b i - matMulVec m G b i) =
        rectMatMulVec dG b := by
    ext i
    simp only [matMulVec, rectMatMulVec, dG]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [haction]
  calc
    vecNorm2 (rectMatMulVec dG b) <=
        frobNormRect dG * vecNorm2 b :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul dG b
    _ <= (theta * invC) * vecNorm2 b :=
      mul_le_mul_of_nonneg_right hdG_norm (vecNorm2_nonneg b)
    _ = theta * (invC * vecNorm2 b) := by ring

/-- On a fixed radius, the componentwise condition number of the nearby
matrix is bounded by the base condition number plus an explicit linear term.

The proof controls the difference of the two absolute matrix products.  The
quadratic cross term is bounded by `theta * rho`, so the displayed coefficient
does not depend on `theta`. -/
theorem higham21_sne_cond2_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    higham21Cond2With
        (higham21Eq21_7ScaledMatrix A D theta)
        (undetAplusOfGramInv
          (higham21Eq21_7ScaledMatrix A D theta) Gtheta) <=
      higham21Cond2With A (undetAplusOfGramInv A G) +
        theta * higham21SNEConditionDifferenceCoefficient
          A D G rho beta := by
  let B : Fin m -> Fin n -> Real :=
    higham21Eq21_7ScaledMatrix A D theta
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramInv A G
  let Bplus : Fin n -> Fin m -> Real := undetAplusOfGramInv B Gtheta
  let P : Fin n -> Fin m -> Real := fun j i => Bplus j i - Aplus j i
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  let cC := higham21SNEConditionDifferenceCoefficient A D G rho beta
  let dAabs : Fin m -> Fin n -> Real :=
    fun i j => |B i j| - |A i j|
  let dPabs : Fin n -> Fin m -> Real :=
    fun j i => |Bplus j i| - |Aplus j i|
  let CA : Fin n -> Fin n -> Real :=
    rectMatMul (absMatrixRect Aplus) (absMatrixRect A)
  let CB : Fin n -> Fin n -> Real :=
    rectMatMul (absMatrixRect Bplus) (absMatrixRect B)
  let E : Fin n -> Fin n -> Real := fun i j => CB i j - CA i j
  have hpC : 0 <= pC := by
    exact higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  have hcC : 0 <= cC := by
    exact higham21_sne_conditionDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  have hPnorm : frobNormRect P <= theta * pC := by
    simpa [B, Aplus, Bplus, P, pC] using
      higham21_sne_pseudoinverse_difference_frobNorm_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta htheta htheta_rho
        hG hGtheta hGtheta_norm
  have hdAabs_norm : frobNormRect dAabs <= theta * frobNormRect D := by
    have hmajorant := frobNormRect_le_of_entry_abs_le
      dAabs (fun i j => theta * |D i j|)
      (by intro i j; exact mul_nonneg htheta (abs_nonneg _))
      (by
        intro i j
        have habs := abs_abs_sub_abs_le_abs_sub (B i j) (A i j)
        calc
          abs (dAabs i j) = abs (abs (B i j) - abs (A i j)) := by rfl
          _ <= |B i j - A i j| := habs
          _ = theta * |D i j| := by
            simp only [B, higham21Eq21_7ScaledMatrix]
            rw [show A i j + theta * D i j - A i j =
              theta * D i j by ring, abs_mul, abs_of_nonneg htheta])
    calc
      frobNormRect dAabs <=
          frobNormRect (fun i j => theta * |D i j|) := hmajorant
      _ = theta * frobNormRect (fun i j => |D i j|) := by
        rw [frobNormRect_smul, abs_of_nonneg htheta]
      _ = theta * frobNormRect D :=
        congrArg (fun z : Real => theta * z) (frobNormRect_abs D)
  have hdPabs_norm : frobNormRect dPabs <= theta * pC := by
    have hmajorant := frobNormRect_le_of_entry_abs_le
      dPabs (absMatrixRect P)
      (by intro j i; exact abs_nonneg _)
      (by
        intro j i
        have habs := abs_abs_sub_abs_le_abs_sub (Bplus j i) (Aplus j i)
        simpa [dPabs, absMatrixRect, P] using habs)
    calc
      frobNormRect dPabs <= frobNormRect (absMatrixRect P) := hmajorant
      _ = frobNormRect P := by
        simpa [absMatrixRect] using (frobNormRect_abs P)
      _ <= theta * pC := hPnorm
  have hBplus_decomp :
      Bplus = fun j i => Aplus j i + P j i := by
    ext j i
    simp only [P]
    ring
  have hBplus_norm :
      frobNormRect Bplus <= frobNormRect Aplus + theta * pC := by
    rw [hBplus_decomp]
    exact (frobNormRect_add_le Aplus P).trans
      (add_le_add (le_refl (frobNormRect Aplus)) hPnorm)
  have hEdecomp :
      E = fun i j =>
        rectMatMul (absMatrixRect Bplus) dAabs i j +
          rectMatMul dPabs (absMatrixRect A) i j := by
    ext i j
    change
      (∑ k : Fin m, |Bplus i k| * |B k j|) -
          ∑ k : Fin m, |Aplus i k| * |A k j| =
        (∑ k : Fin m, |Bplus i k| * (|B k j| - |A k j|)) +
          ∑ k : Fin m,
            (|Bplus i k| - |Aplus i k|) * |A k j|
    calc
      (∑ k : Fin m, |Bplus i k| * |B k j|) -
          ∑ k : Fin m, |Aplus i k| * |A k j| =
        ∑ k : Fin m,
          (|Bplus i k| * |B k j| - |Aplus i k| * |A k j|) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Fin m,
          (|Bplus i k| * (|B k j| - |A k j|) +
            (|Bplus i k| - |Aplus i k|) * |A k j|) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = (∑ k : Fin m, |Bplus i k| * (|B k j| - |A k j|)) +
          ∑ k : Fin m,
            (|Bplus i k| - |Aplus i k|) * |A k j| := by
            rw [Finset.sum_add_distrib]
  have hE_norm : frobNormRect E <= theta * cC := by
    rw [hEdecomp]
    calc
      frobNormRect
          (fun i j =>
            rectMatMul (absMatrixRect Bplus) dAabs i j +
              rectMatMul dPabs (absMatrixRect A) i j) <=
        frobNormRect (rectMatMul (absMatrixRect Bplus) dAabs) +
          frobNormRect (rectMatMul dPabs (absMatrixRect A)) :=
        frobNormRect_add_le _ _
      _ <= frobNormRect (absMatrixRect Bplus) * frobNormRect dAabs +
          frobNormRect dPabs * frobNormRect (absMatrixRect A) :=
        add_le_add
          (frobNormRect_rectMatMul_le (absMatrixRect Bplus) dAabs)
          (frobNormRect_rectMatMul_le dPabs (absMatrixRect A))
      _ = frobNormRect Bplus * frobNormRect dAabs +
          frobNormRect dPabs * frobNormRect A := by
        rw [show frobNormRect (absMatrixRect Bplus) = frobNormRect Bplus by
          simpa [absMatrixRect] using frobNormRect_abs Bplus]
        rw [show frobNormRect (absMatrixRect A) = frobNormRect A by
          simpa [absMatrixRect] using frobNormRect_abs A]
      _ <= (frobNormRect Aplus + theta * pC) *
            (theta * frobNormRect D) +
          (theta * pC) * frobNormRect A := by
        apply add_le_add
        · calc
            frobNormRect Bplus * frobNormRect dAabs <=
                (frobNormRect Aplus + theta * pC) *
                  frobNormRect dAabs :=
              mul_le_mul_of_nonneg_right hBplus_norm
                (frobNormRect_nonneg dAabs)
            _ <= (frobNormRect Aplus + theta * pC) *
                  (theta * frobNormRect D) :=
              mul_le_mul_of_nonneg_left hdAabs_norm
                (add_nonneg (frobNormRect_nonneg Aplus)
                  (mul_nonneg htheta hpC))
        · exact mul_le_mul_of_nonneg_right hdPabs_norm
            (frobNormRect_nonneg A)
      _ = theta *
          (frobNormRect Aplus * frobNormRect D +
            pC * frobNormRect A + theta * pC * frobNormRect D) := by
        ring
      _ <= theta *
          (frobNormRect Aplus * frobNormRect D +
            pC * frobNormRect A + rho * pC * frobNormRect D) := by
        apply mul_le_mul_of_nonneg_left _ htheta
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right htheta_rho hpC)
            (frobNormRect_nonneg D))
      _ = theta * cC := by
        simp only [cC, higham21SNEConditionDifferenceCoefficient,
          Aplus, pC]
  have hCAop :
      rectOpNorm2Le CA (higham21Cond2With A Aplus) := by
    simpa [CA, higham21Cond2With] using
      rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le CA le_rfl
  have hsum_eq : (fun i j => CA i j + E i j) = CB := by
    ext i j
    simp only [E]
    ring
  have hCBop :
      rectOpNorm2Le CB
        (higham21Cond2With A Aplus + theta * cC) := by
    have h := rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
      CA E hCAop hE_norm
    rw [hsum_eq] at h
    exact h
  have hcoefficient :
      0 <= higham21Cond2With A Aplus + theta * cC :=
    add_nonneg (higham21Cond2With_nonneg A Aplus) (mul_nonneg htheta hcC)
  have hCBcomplex :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
      CB hcoefficient hCBop
  simpa [B, Aplus, Bplus, CB, cC, higham21Cond2With] using hCBcomplex

/-- The exact nearby minimum-norm solution for the unchanged right-hand side
has norm at most the base solution norm plus a fixed-radius linear term. -/
theorem higham21_sne_solution_norm_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    vecNorm2
        (rectMatMulVec
          (undetAplusOfGramInv
            (higham21Eq21_7ScaledMatrix A D theta) Gtheta) b) <=
      vecNorm2 (rectMatMulVec (undetAplusOfGramInv A G) b) +
        theta *
          (higham21SNEPseudoinverseDifferenceCoefficient
            A D G rho beta * vecNorm2 b) := by
  let B : Fin m -> Fin n -> Real :=
    higham21Eq21_7ScaledMatrix A D theta
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramInv A G
  let Bplus : Fin n -> Fin m -> Real := undetAplusOfGramInv B Gtheta
  let P : Fin n -> Fin m -> Real := fun j i => Bplus j i - Aplus j i
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  have hPnorm : frobNormRect P <= theta * pC := by
    simpa [B, Aplus, Bplus, P, pC] using
      higham21_sne_pseudoinverse_difference_frobNorm_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta htheta htheta_rho
        hG hGtheta hGtheta_norm
  have haction :
      rectMatMulVec Bplus b =
        fun j => rectMatMulVec Aplus b j + rectMatMulVec P b j := by
    ext j
    simp only [rectMatMulVec, P]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change vecNorm2 (rectMatMulVec Bplus b) <=
    vecNorm2 (rectMatMulVec Aplus b) + theta * (pC * vecNorm2 b)
  rw [haction]
  calc
    vecNorm2
        (fun j => rectMatMulVec Aplus b j + rectMatMulVec P b j) <=
      vecNorm2 (rectMatMulVec Aplus b) +
        vecNorm2 (rectMatMulVec P b) :=
      vecNorm2_add_le _ _
    _ <= vecNorm2 (rectMatMulVec Aplus b) +
        frobNormRect P * vecNorm2 b :=
      add_le_add (le_refl _)
        (vecNorm2_rectMatMulVec_le_frobNormRect_mul P b)
    _ <= vecNorm2 (rectMatMulVec Aplus b) +
        (theta * pC) * vecNorm2 b :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hPnorm (vecNorm2_nonneg b))
    _ = vecNorm2 (rectMatMulVec Aplus b) +
        theta * (pC * vecNorm2 b) := by ring

/-- Strong fixed-radius transfer of the SNE condition expression.

For `B(theta) = A + theta D`, the exact nearby quantity
`cond2(B(theta)) * ||B(theta)^+ b||_2` is bounded by the corresponding base
quantity plus `theta` times a coefficient depending only on the fixed radius
and the uniform inverse envelope. -/
theorem higham21_sne_cond2_mul_solution_norm_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    higham21Cond2With
          (higham21Eq21_7ScaledMatrix A D theta)
          (undetAplusOfGramInv
            (higham21Eq21_7ScaledMatrix A D theta) Gtheta) *
        vecNorm2
          (rectMatMulVec
            (undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta) b) <=
      higham21Cond2With A (undetAplusOfGramInv A G) *
          vecNorm2 (rectMatMulVec (undetAplusOfGramInv A G) b) +
        theta * higham21SNEConditionTransferCoefficient
          A D b G rho beta := by
  let B : Fin m -> Fin n -> Real :=
    higham21Eq21_7ScaledMatrix A D theta
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramInv A G
  let Bplus : Fin n -> Fin m -> Real := undetAplusOfGramInv B Gtheta
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let xtheta : Fin n -> Real := rectMatMulVec Bplus b
  let condA := higham21Cond2With A Aplus
  let condB := higham21Cond2With B Bplus
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  let cC := higham21SNEConditionDifferenceCoefficient A D G rho beta
  have hpC : 0 <= pC :=
    higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  have hcC : 0 <= cC :=
    higham21_sne_conditionDifferenceCoefficient_nonneg
      A D G rho beta hrho hbeta
  have hcondA : 0 <= condA := higham21Cond2With_nonneg A Aplus
  have hcond : condB <= condA + theta * cC := by
    simpa [B, Aplus, Bplus, condA, condB, cC] using
      higham21_sne_cond2_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta htheta htheta_rho
        hG hGtheta hGtheta_norm
  have hsolution :
      vecNorm2 xtheta <= vecNorm2 x + theta * (pC * vecNorm2 b) := by
    simpa [B, Aplus, Bplus, x, xtheta, pC] using
      higham21_sne_solution_norm_le_fixed_radius
        A D b G Gtheta rho beta theta hrho hbeta htheta htheta_rho
        hG hGtheta hGtheta_norm
  change condB * vecNorm2 xtheta <=
    condA * vecNorm2 x +
      theta * higham21SNEConditionTransferCoefficient A D b G rho beta
  calc
    condB * vecNorm2 xtheta <=
        (condA + theta * cC) * vecNorm2 xtheta :=
      mul_le_mul_of_nonneg_right hcond (vecNorm2_nonneg xtheta)
    _ <= (condA + theta * cC) *
        (vecNorm2 x + theta * (pC * vecNorm2 b)) :=
      mul_le_mul_of_nonneg_left hsolution
        (add_nonneg hcondA (mul_nonneg htheta hcC))
    _ = condA * vecNorm2 x + theta *
        (cC * vecNorm2 x + condA * (pC * vecNorm2 b) +
          theta * cC * (pC * vecNorm2 b)) := by
      ring
    _ <= condA * vecNorm2 x + theta *
        (cC * vecNorm2 x + condA * (pC * vecNorm2 b) +
          rho * cC * (pC * vecNorm2 b)) := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left _ htheta
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htheta_rho hcC)
          (mul_nonneg hpC (vecNorm2_nonneg b)))
    _ = condA * vecNorm2 x +
        theta * higham21SNEConditionTransferCoefficient
          A D b G rho beta := by
      simp only [higham21SNEConditionTransferCoefficient,
        condA, Aplus, x, pC, cC]

/-- Fixed-radius vector form of the pseudoinverse-difference estimate. -/
theorem higham21_sne_primal_solution_difference_vecNorm2_le_fixed_radius
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real)
    (G Gtheta : Fin m -> Fin m -> Real)
    (rho beta theta : Real)
    (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (htheta : 0 <= theta) (htheta_rho : theta <= rho)
    (hG : IsInverse m (rectGram A) G)
    (hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta)
    (hGtheta_norm : frobNorm Gtheta <= beta) :
    vecNorm2 (fun j =>
        rectMatMulVec
            (undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta) b j -
          rectMatMulVec (undetAplusOfGramInv A G) b j) <=
      theta *
        (higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta *
          vecNorm2 b) := by
  let B : Fin m -> Fin n -> Real := higham21Eq21_7ScaledMatrix A D theta
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramInv A G
  let Bplus : Fin n -> Fin m -> Real := undetAplusOfGramInv B Gtheta
  let P : Fin n -> Fin m -> Real := fun j i => Bplus j i - Aplus j i
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D G rho beta
  have hP : frobNormRect P <= theta * pC := by
    simpa [B, Aplus, Bplus, P, pC] using
      higham21_sne_pseudoinverse_difference_frobNorm_le_fixed_radius
        A D G Gtheta rho beta theta hrho hbeta htheta htheta_rho
          hG hGtheta hGtheta_norm
  have haction :
      (fun j => rectMatMulVec Bplus b j - rectMatMulVec Aplus b j) =
        rectMatMulVec P b := by
    ext j
    simp only [rectMatMulVec, P]
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change vecNorm2
      (fun j => rectMatMulVec Bplus b j - rectMatMulVec Aplus b j) <=
    theta * (pC * vecNorm2 b)
  rw [haction]
  calc
    vecNorm2 (rectMatMulVec P b) <= frobNormRect P * vecNorm2 b :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul P b
    _ <= (theta * pC) * vecNorm2 b :=
      mul_le_mul_of_nonneg_right hP (vecNorm2_nonneg b)
    _ = theta * (pC * vecNorm2 b) := by ring

/-- The automatically derived direction radius discharges every inverse and
inverse-envelope hypothesis in the dual-vector transfer theorem. -/
theorem higham21_sne_dual_solution_difference_vecNorm2_le_direction_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (theta : Real)
    (hm : 0 < m)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (htheta : 0 <= theta)
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, |D i j| <= E i j)
    (htheta_radius : theta <= higham21PerturbationDirectionRadius A D E) :
    let G := undetGramNonsingInv A
    let Gtheta :=
      undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
    vecNorm2
        (fun i => matMulVec m Gtheta b i - matMulVec m G b i) <=
      theta *
        (higham21Eq21_7InverseDifferenceCoefficient A D G
            (higham21PerturbationDirectionRadius A D E)
            (higham21PerturbationGramInverseBound A) * vecNorm2 b) := by
  dsimp only
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let G := undetGramNonsingInv A
  let Gtheta :=
    undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  have htheta_abs : |theta| <= radius := by
    simpa [abs_of_nonneg htheta, radius] using htheta_radius
  have hthetaCert := hcert.2.2 theta htheta_abs
  have hG : IsInverse m (rectGram A) G := by
    simpa [G, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta := by
    simpa [Gtheta, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m
        (rectGram (higham21Eq21_7ScaledMatrix A D theta)) hthetaCert.1
  simpa [G, Gtheta, radius, beta] using
    higham21_sne_dual_solution_difference_vecNorm2_le_fixed_radius
      A D b G Gtheta radius beta theta hcert.1.le hcert.2.1
        htheta htheta_radius hG hGtheta hthetaCert.2

/-- Direction-radius wrapper for the exact minimum-norm solution difference. -/
theorem higham21_sne_primal_solution_difference_vecNorm2_le_direction_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (theta : Real)
    (hm : 0 < m)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (htheta : 0 <= theta)
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, |D i j| <= E i j)
    (htheta_radius : theta <= higham21PerturbationDirectionRadius A D E) :
    let G := undetGramNonsingInv A
    let Gtheta :=
      undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
    vecNorm2 (fun j =>
        rectMatMulVec
            (undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta) b j -
          rectMatMulVec (undetAplusOfGramInv A G) b j) <=
      theta *
        (higham21SNEPseudoinverseDifferenceCoefficient A D G
          (higham21PerturbationDirectionRadius A D E)
          (higham21PerturbationGramInverseBound A) * vecNorm2 b) := by
  dsimp only
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let G := undetGramNonsingInv A
  let Gtheta :=
    undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  have htheta_abs : |theta| <= radius := by
    simpa [abs_of_nonneg htheta, radius] using htheta_radius
  have hthetaCert := hcert.2.2 theta htheta_abs
  have hG : IsInverse m (rectGram A) G := by
    simpa [G, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta := by
    simpa [Gtheta, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m
        (rectGram (higham21Eq21_7ScaledMatrix A D theta)) hthetaCert.1
  simpa [G, Gtheta, radius, beta] using
    higham21_sne_primal_solution_difference_vecNorm2_le_fixed_radius
      A D b G Gtheta radius beta theta hcert.1.le hcert.2.1
        htheta htheta_radius hG hGtheta hthetaCert.2

/-- Direction-radius wrapper for the complete source condition-product
transfer. -/
theorem higham21_sne_cond2_mul_solution_norm_le_direction_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (theta : Real)
    (hm : 0 < m)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (htheta : 0 <= theta)
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, |D i j| <= E i j)
    (htheta_radius : theta <= higham21PerturbationDirectionRadius A D E) :
    let G := undetGramNonsingInv A
    let Gtheta :=
      undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
    higham21Cond2With
          (higham21Eq21_7ScaledMatrix A D theta)
          (undetAplusOfGramInv
            (higham21Eq21_7ScaledMatrix A D theta) Gtheta) *
        vecNorm2
          (rectMatMulVec
            (undetAplusOfGramInv
              (higham21Eq21_7ScaledMatrix A D theta) Gtheta) b) <=
      higham21Cond2With A (undetAplusOfGramInv A G) *
          vecNorm2 (rectMatMulVec (undetAplusOfGramInv A G) b) +
        theta * higham21SNEConditionTransferCoefficient A D b G
          (higham21PerturbationDirectionRadius A D E)
          (higham21PerturbationGramInverseBound A) := by
  dsimp only
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let G := undetGramNonsingInv A
  let Gtheta :=
    undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D theta)
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  have htheta_abs : |theta| <= radius := by
    simpa [abs_of_nonneg htheta, radius] using htheta_radius
  have hthetaCert := hcert.2.2 theta htheta_abs
  have hG : IsInverse m (rectGram A) G := by
    simpa [G, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hGtheta : IsInverse m
      (rectGram (higham21Eq21_7ScaledMatrix A D theta)) Gtheta := by
    simpa [Gtheta, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m
        (rectGram (higham21Eq21_7ScaledMatrix A D theta)) hthetaCert.1
  simpa [G, Gtheta, radius, beta] using
    higham21_sne_cond2_mul_solution_norm_le_fixed_radius
      A D b G Gtheta radius beta theta hcert.1.le hcert.2.1
        htheta htheta_radius hG hGtheta hthetaCert.2

end NumStability
