import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Radius.Core
import NumStability.Source.Higham.Chapter21.Equation07.ConditionTransfer

/-!
# Algorithms.Underdetermined.Higham21SNEConditionTransfer

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Fixed-radius transfer of the SNE componentwise condition expression.



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
