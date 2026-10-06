import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.Uniform
import NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.EndToEnd.Core
import NumStability.Source.Higham.Chapter21.Equation11.Uniform
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Uniform

/-!
# Algorithms.Underdetermined.Higham21SNEUniform

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Fixed-radius uniform closure for the Householder SNE path.




namespace NumStability

open scoped BigOperators

set_option maxHeartbeats 1200000

/-!
# Fixed-radius uniform SNE closure

The finite endpoint in `Higham21SNEClosure` keeps a completely explicit
second-order coefficient, but that coefficient follows the active QR
direction and the active rounded normal solution.  This file freezes those
quantities on a source-defined perturbation neighborhood.
-/









/-! ## Q-method fixed-radius coefficients

The following coefficients use the existing direction-independent rowwise
Q-method neighborhood.  They depend only on `A`, `b`, the dimensions, and the
chosen fixed master radius `tau`.
-/









































































































































































































/-- The fixed Q-method contraction supplies a direction-independent bound for
the Gram inverse of the concrete nearby Householder matrix. -/
theorem higham21_sne_householder_nearby_gramInverse_frobNorm_le_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real) (htau : 0 <= tau)
    (hrho_tau : higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    frobNorm (undetGramNonsingInv B) <= higham21SNEQUniformBeta A tau := by
  dsimp only
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i := by
    simpa [rho, F, D] using
      higham21_sne_householder_normalized_direction_rowNorm_le
        fp A hm hvalidQR hrho_pos
  have hscaled : higham21Eq21_7ScaledMatrix A D rho = B := by
    ext i j
    dsimp [higham21Eq21_7ScaledMatrix, D, B]
    rw [mul_div_cancel₀ _ (ne_of_gt hrho_pos)]
  have hbound := higham21Eq21_11_scaled_gramInverse_frobNorm_le_uniform
    A D tau rho hm hdet htau hrho
      (by simpa [rho] using hrho_tau) hrow hgram
  rw [hscaled] at hbound
  simpa [B, higham21SNEQUniformBeta] using hbound












































































































































































































































































































































































/-- Fixed-radius source transfers for the exact Householder QR reference.
All three displayed coefficients depend only on `A`, `b`, and the chosen
master radius `tau`, not on the active Householder perturbation. -/
theorem higham21_sne_householder_reference_transfers_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real) (htau : 0 <= tau)
    (hrho_tau : higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let y := rectMatMulVec (undetGramNonsingInv A) b
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let Ky := higham21SNEQUniformInverseDifferenceCoefficient A tau * vecNorm2 b
    let Kx := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau *
      vecNorm2 b
    let Kc := higham21SNEQUniformConditionTransferCoefficient A b tau
    vecNorm2 (fun i => ybar i - y i) <= rho * Ky /\
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx /\
      higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar <=
        higham21SNEQUniformSourceQuantity A b + rho * Kc := by
  dsimp only
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let GA := undetGramNonsingInv A
  let GB := undetGramNonsingInv B
  let beta := higham21SNEQUniformBeta A tau
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let y := rectMatMulVec GA b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let invC := higham21Eq21_7InverseDifferenceCoefficient A D GA tau beta
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D GA tau beta
  let cC := higham21SNEConditionTransferCoefficient A D b GA tau beta
  have hrho : 0 <= rho := hrho_pos.le
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i := by
    simpa [rho, F, D] using
      higham21_sne_householder_normalized_direction_rowNorm_le
        fp A hm hvalidQR hrho_pos
  have hscaled : higham21Eq21_7ScaledMatrix A D rho = B := by
    ext i j
    dsimp [higham21Eq21_7ScaledMatrix, D, B]
    rw [mul_div_cancel₀ _ (ne_of_gt hrho_pos)]
  have hAinv : IsInverse m (rectGram A) GA := by
    simpa [GA, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hGram : rectGram B = rectMatMul (finiteTranspose R) R :=
    higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hGB : GB = rectMatMul Rinv (finiteTranspose Rinv) := by
    dsimp [GB, undetGramNonsingInv]
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv
  have hBright : IsRightInverse m (rectGram B) GB := by
    intro i j
    rw [hGram, hGB]
    exact IsRightInverse_rectMatMul_transpose_self_of_IsInverse hInv i j
  have hBinv : IsInverse m (rectGram B) GB :=
    ⟨isLeftInverse_of_isRightInverse (rectGram B) GB hBright, hBright⟩
  have hGBnorm : frobNorm GB <= beta := by
    simpa [GB, beta, B, F] using
      higham21_sne_householder_nearby_gramInverse_frobNorm_le_q_uniform
        fp A hm hvalidQR hdet hrho_pos tau htau hrho_tau hgram
  have hyRaw := higham21_sne_dual_solution_difference_vecNorm2_le_fixed_radius
    A D b GA GB tau beta rho htau hbeta hrho hrho_tau hAinv
      (by simpa [hscaled] using hBinv) hGBnorm
  have hxRaw := higham21_sne_primal_solution_difference_vecNorm2_le_fixed_radius
    A D b GA GB tau beta rho htau hbeta hrho hrho_tau hAinv
      (by simpa [hscaled] using hBinv) hGBnorm
  have hqRaw := higham21_sne_cond2_mul_solution_norm_le_fixed_radius
    A D b GA GB tau beta rho htau hbeta hrho hrho_tau hAinv
      (by simpa [hscaled] using hBinv) hGBnorm
  have hybar : ybar = rectMatMulVec GB b := by
    simpa [ybar, GB, B, F] using
      higham21_sne_householder_referenceY_eq_nearby_gram_inverse
        fp A b hm hvalidQR hdiag
  have hxbar : xbar = rectMatMulVec (undetAplusOfGramNonsingInv B) b := by
    simpa [xbar, B, F] using
      higham21_sne_householder_referenceOutput_eq_nearby_pseudoinverse
        fp A b hm hvalidQR hdiag
  have hinv : invC <= higham21SNEQUniformInverseDifferenceCoefficient A tau := by
    simpa [invC, GA, beta] using
      higham21_sne_inverseDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  have hp : pC <= higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau := by
    simpa [pC, GA, beta] using
      higham21_sne_pseudoinverseDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  have hc : cC <= higham21SNEQUniformConditionTransferCoefficient A b tau := by
    simpa [cC, GA, beta] using
      higham21_sne_conditionTransferCoefficient_le_q_uniform
        A D b tau htau hgram hrow
  constructor
  . change vecNorm2 (fun i => ybar i - y i) <=
      rho * (higham21SNEQUniformInverseDifferenceCoefficient A tau *
        vecNorm2 b)
    rw [hybar]
    calc
      vecNorm2 (fun i => rectMatMulVec GB b i - y i) <=
          rho * (invC * vecNorm2 b) := by
        simpa [GA, GB, y, invC, matMulVec, rectMatMulVec] using hyRaw
      _ <= rho *
          (higham21SNEQUniformInverseDifferenceCoefficient A tau *
            vecNorm2 b) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hinv (vecNorm2_nonneg b)) hrho
  constructor
  . change vecNorm2 (fun j => xbar j - x j) <=
      rho * (higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau *
        vecNorm2 b)
    rw [hxbar]
    calc
      vecNorm2 (fun j =>
          rectMatMulVec (undetAplusOfGramNonsingInv B) b j - x j) <=
          rho * (pC * vecNorm2 b) := by
        simpa [GA, GB, x, pC, hscaled,
          undetAplusOfGramNonsingInv, undetAplusOfGramInv] using hxRaw
      _ <= rho *
          (higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau *
            vecNorm2 b) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (vecNorm2_nonneg b)) hrho
  . change higham21Cond2With B (undetAplusOfGramNonsingInv B) *
      vecNorm2 xbar <= higham21SNEQUniformSourceQuantity A b +
        rho * higham21SNEQUniformConditionTransferCoefficient A b tau
    rw [hxbar]
    calc
      higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv B) b) <=
        higham21SNEQUniformSourceQuantity A b + rho * cC := by
          simpa [GA, GB, x, cC, hscaled,
            higham21SNEQUniformSourceQuantity,
            undetAplusOfGramNonsingInv, undetAplusOfGramInv] using hqRaw
      _ <= higham21SNEQUniformSourceQuantity A b +
          rho * higham21SNEQUniformConditionTransferCoefficient A b tau :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hc hrho)














































































/-- The inverse triangular factor is also uniformly bounded on the fixed
source neighborhood. -/
theorem higham21_sne_householder_RInv_frobNorm_le_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real) (htau : 0 <= tau)
    (hrho_tau : higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    frobNorm (higham21SNEHouseholderRInv fp A) <=
      higham21SNEQUniformRInvBound A tau := by
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let GB := undetGramNonsingInv B
  let beta := higham21SNEQUniformBeta A tau
  let BR := higham21SNEQUniformRBound A tau
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hGram : rectGram B = rectMatMul (finiteTranspose R) R :=
    higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hGB : GB = rectMatMul Rinv (finiteTranspose Rinv) := by
    dsimp [GB, undetGramNonsingInv]
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv
  have hTInv := isInverse_finiteTranspose hInv
  have hrecover : Rinv = rectMatMul GB (finiteTranspose R) := by
    calc
      Rinv = rectMatMul Rinv (idMatrix m) := (rectMatMul_id_right Rinv).symm
      _ = rectMatMul Rinv
          (rectMatMul (finiteTranspose Rinv) (finiteTranspose R)) := by
        rw [show rectMatMul (finiteTranspose Rinv) (finiteTranspose R) =
            idMatrix m by
          ext i j
          exact hTInv.1 i j]
      _ = rectMatMul (rectMatMul Rinv (finiteTranspose Rinv))
          (finiteTranspose R) :=
        (rectMatMul_assoc Rinv (finiteTranspose Rinv) (finiteTranspose R)).symm
      _ = rectMatMul GB (finiteTranspose R) := by rw [hGB]
  have hGBnorm : frobNorm GB <= beta := by
    simpa [GB, beta, B, F] using
      higham21_sne_householder_nearby_gramInverse_frobNorm_le_q_uniform
        fp A hm hvalidQR hdet hrho_pos tau htau hrho_tau hgram
  have hRnorm : frobNorm R <= BR := by
    simpa [R, BR] using
      higham21_sne_householder_R_frobNorm_le_q_uniform
        fp A hm hvalidQR hrho_pos tau hrho_tau
  change frobNorm Rinv <= higham21SNEQUniformRInvBound A tau
  rw [hrecover]
  calc
    frobNorm (rectMatMul GB (finiteTranspose R)) <=
        frobNorm GB * frobNorm (finiteTranspose R) :=
      frobNorm_matMul_le GB (finiteTranspose R)
    _ = frobNorm GB * frobNorm R := by
      congr 1
      rw [<- frobNormRect_eq_frobNormFn, frobNormRect_finiteTranspose,
        frobNormRect_eq_frobNormFn]
    _ <= beta * BR :=
      mul_le_mul hGBnorm hRnorm (frobNorm_nonneg R) hbeta
    _ = higham21SNEQUniformRInvBound A tau := rfl

/-- Under an explicit fixed-radius nonbreakdown margin, the rounded dual
normal-equation solution is uniformly bounded by source data. -/
theorem higham21_sne_householder_computedNormalSolution_vecNorm2_le_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2) :
    vecNorm2 (higham21SNEComputedNormalSolution fp m
      (higham21SNEHouseholderRHat fp A) b) <=
      higham21SNEQUniformYHatBound A b tau := by
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let beta := higham21SNEQUniformBeta A tau
  let BR := higham21SNEQUniformRBound A tau
  let BI := higham21SNEQUniformRInvBound A tau
  let MU := higham21SNEQUniformSolveMultiplier A tau
  let M := frobNorm Rinv *
    (frobNorm R + frobNorm Rinv * frobNorm R *
      (frobNorm R + theta * frobNorm R))
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have hrho : 0 <= rho := hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hgamma_theta : gammaM <= theta := by dsimp [theta]; linarith
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have htheta_tau' : theta <= tau := by simpa [theta, gammaM, rho] using htheta_tau
  have htau : 0 <= tau := htheta.trans htheta_tau'
  have hrho_tau : rho <= tau := hrho_theta.trans htheta_tau'
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hBR0 : 0 <= BR := by
    dsimp [BR, higham21SNEQUniformRBound]
    exact add_nonneg (frobNorm_nonneg A)
      (mul_nonneg htau (by
        dsimp [higham21SNEQUniformDirectionFrob,
          higham21Eq21_11UniformDirectionFrobBound]
        exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)))
  have hBI0 : 0 <= BI := by
    dsimp [BI, higham21SNEQUniformRInvBound]
    exact mul_nonneg hbeta hBR0
  have hR : frobNorm R <= BR := by
    simpa [R, BR, rho] using
      higham21_sne_householder_R_frobNorm_le_q_uniform
        fp A hm hvalidQR hrho_pos tau (by simpa [rho] using hrho_tau)
  have hRI : frobNorm Rinv <= BI := by
    simpa [Rinv, BI, rho] using
      higham21_sne_householder_RInv_frobNorm_le_q_uniform
        fp A hm hvalidQR hdiag hdet hrho_pos tau htau
          (by simpa [rho] using hrho_tau) hgram
  have hR0 : 0 <= frobNorm R := frobNorm_nonneg R
  have hRI0 : 0 <= frobNorm Rinv := frobNorm_nonneg Rinv
  have hinner0 : 0 <= frobNorm R + theta * frobNorm R :=
    add_nonneg hR0 (mul_nonneg htheta hR0)
  have hinnerU0 : 0 <= BR + tau * BR :=
    add_nonneg hBR0 (mul_nonneg htau hBR0)
  have houter0 : 0 <= frobNorm R + frobNorm Rinv * frobNorm R *
      (frobNorm R + theta * frobNorm R) :=
    add_nonneg hR0 (mul_nonneg (mul_nonneg hRI0 hR0) hinner0)
  have hM : M <= MU := by
    have hIR : frobNorm Rinv * frobNorm R <= BI * BR :=
      mul_le_mul hRI hR hR0 hBI0
    have hinner : frobNorm R + theta * frobNorm R <= BR + tau * BR :=
      add_le_add hR (mul_le_mul htheta_tau' hR hR0 htau)
    have hprod : frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R) <=
        BI * BR * (BR + tau * BR) :=
      mul_le_mul hIR hinner hinner0 (mul_nonneg hBI0 hBR0)
    have houter : frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R) <=
        BR + BI * BR * (BR + tau * BR) := add_le_add hR hprod
    change frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) <=
      BI * (BR + BI * BR * (BR + tau * BR))
    exact mul_le_mul hRI houter houter0 hBI0
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hDeltaR1theta : forall i j,
      |DeltaR1 i j| <= theta * |R i j| := by
    intro i j
    exact (hDeltaR1 i j).trans
      (mul_le_mul_of_nonneg_right hgamma_theta (abs_nonneg _))
  have hDeltaR2theta : forall i j,
      |DeltaR2 i j| <= theta * |R i j| := by
    intro i j
    exact (hDeltaR2 i j).trans
      (mul_le_mul_of_nonneg_right hgamma_theta (abs_nonneg _))
  have hdiff : vecNorm2 (fun i => ybar i - yhat i) <= theta * (M * vecNorm2 yhat) := by
    simpa [M] using
      higham21_dh1993_factor_difference_vecNorm2_le_radius
        theta theta htheta le_rfl R Rinv DeltaR1 DeltaR2 ybar yhat
          hInv hNormal hDeltaR1theta hDeltaR2theta
  have hM0 : 0 <= M := by
    dsimp [M]
    exact mul_nonneg hRI0 houter0
  have hMU0 : 0 <= MU := hM0.trans hM
  have hdiffHalf : vecNorm2 (fun i => ybar i - yhat i) <=
      (1 / 2 : Real) * vecNorm2 yhat := by
    calc
      vecNorm2 (fun i => ybar i - yhat i) <= theta * (M * vecNorm2 yhat) := hdiff
      _ <= theta * (MU * vecNorm2 yhat) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hM (vecNorm2_nonneg yhat)) htheta
      _ <= tau * (MU * vecNorm2 yhat) :=
        mul_le_mul_of_nonneg_right htheta_tau'
          (mul_nonneg hMU0 (vecNorm2_nonneg yhat))
      _ = (tau * MU) * vecNorm2 yhat := by ring
      _ <= (1 / 2 : Real) * vecNorm2 yhat :=
        mul_le_mul_of_nonneg_right hmargin (vecNorm2_nonneg yhat)
  have hGB : frobNorm (undetGramNonsingInv B) <= beta := by
    simpa [B, F, beta, rho] using
      higham21_sne_householder_nearby_gramInverse_frobNorm_le_q_uniform
        fp A hm hvalidQR hdet hrho_pos tau htau
          (by simpa [rho] using hrho_tau) hgram
  have hybarEq : ybar = rectMatMulVec (undetGramNonsingInv B) b := by
    simpa [ybar, B, F] using
      higham21_sne_householder_referenceY_eq_nearby_gram_inverse
        fp A b hm hvalidQR hdiag
  have hybarBound : vecNorm2 ybar <= beta * vecNorm2 b := by
    rw [hybarEq]
    calc
      vecNorm2 (rectMatMulVec (undetGramNonsingInv B) b) <=
          frobNormRect (undetGramNonsingInv B) * vecNorm2 b :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul
          (undetGramNonsingInv B) b
      _ = frobNorm (undetGramNonsingInv B) * vecNorm2 b := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= beta * vecNorm2 b :=
        mul_le_mul_of_nonneg_right hGB (vecNorm2_nonneg b)
  have htriangle : vecNorm2 yhat <= vecNorm2 ybar +
      vecNorm2 (fun i => ybar i - yhat i) := by
    calc
      vecNorm2 yhat = vecNorm2 (fun i => ybar i - (ybar i - yhat i)) := by
        congr 1
        funext i
        ring
      _ <= vecNorm2 ybar + vecNorm2 (fun i => -(ybar i - yhat i)) :=
        vecNorm2_add_le ybar (fun i => -(ybar i - yhat i))
      _ = vecNorm2 ybar + vecNorm2 (fun i => ybar i - yhat i) := by
        congr 1
        simpa using vecNorm2_neg (fun i => ybar i - yhat i)
  have hpre : vecNorm2 yhat <= beta * vecNorm2 b +
      (1 / 2 : Real) * vecNorm2 yhat :=
    htriangle.trans (add_le_add hybarBound hdiffHalf)
  change vecNorm2 yhat <= higham21SNEQUniformYHatBound A b tau
  dsimp [higham21SNEQUniformYHatBound, beta]
  nlinarith [mul_nonneg hbeta (vecNorm2_nonneg b), vecNorm2_nonneg yhat]

/-- The active dual-displacement and signed-remainder coefficients in the
finite SNE bound are dominated by fixed source-neighborhood coefficients. -/
theorem higham21_sne_householder_actual_coefficients_le_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2) :
    let theta := gamma fp m + higham21SNEHouseholderRho fp m k
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let Kd := frobNorm Rinv *
      (frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
    let Crem := frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
    Kd <= higham21SNEQUniformKd A b tau /\
      Crem <= higham21SNEQUniformSignedRemainder A b tau := by
  dsimp only
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let BR := higham21SNEQUniformRBound A tau
  let BI := higham21SNEQUniformRInvBound A tau
  let BY := higham21SNEQUniformYHatBound A b tau
  let MU := higham21SNEQUniformSolveMultiplier A tau
  let BKd := higham21SNEQUniformKd A b tau
  let M := frobNorm Rinv *
    (frobNorm R + frobNorm Rinv * frobNorm R *
      (frobNorm R + theta * frobNorm R))
  let Kd := M * vecNorm2 yhat
  let Crem := frobNorm R * Kd +
    frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
    frobNorm A * Kd
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have hrho : 0 <= rho := hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have htheta_tau' : theta <= tau := by simpa [theta, gammaM, rho] using htheta_tau
  have htau : 0 <= tau := htheta.trans htheta_tau'
  have hrho_tau : rho <= tau := hrho_theta.trans htheta_tau'
  have hbeta : 0 <= higham21SNEQUniformBeta A tau :=
    higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hd0 : 0 <= higham21SNEQUniformDirectionFrob A := by
    dsimp [higham21SNEQUniformDirectionFrob,
      higham21Eq21_11UniformDirectionFrobBound]
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)
  have hBR0 : 0 <= BR := by
    dsimp [BR, higham21SNEQUniformRBound]
    exact add_nonneg (frobNorm_nonneg A) (mul_nonneg htau hd0)
  have hBI0 : 0 <= BI := by
    dsimp [BI, higham21SNEQUniformRInvBound]
    exact mul_nonneg hbeta hBR0
  have hBY0 : 0 <= BY := by
    dsimp [BY, higham21SNEQUniformYHatBound]
    exact mul_nonneg (mul_nonneg (by norm_num) hbeta) (vecNorm2_nonneg b)
  have hR : frobNorm R <= BR := by
    simpa [R, BR, rho] using
      higham21_sne_householder_R_frobNorm_le_q_uniform
        fp A hm hvalidQR hrho_pos tau (by simpa [rho] using hrho_tau)
  have hRI : frobNorm Rinv <= BI := by
    simpa [Rinv, BI, rho] using
      higham21_sne_householder_RInv_frobNorm_le_q_uniform
        fp A hm hvalidQR hdiag hdet hrho_pos tau htau
          (by simpa [rho] using hrho_tau) hgram
  have hY : vecNorm2 yhat <= BY := by
    simpa [yhat, R, BY, rho, gammaM] using
      higham21_sne_householder_computedNormalSolution_vecNorm2_le_q_uniform
        fp A b hm hvalidQR hmGamma hdiag hdet hrho_pos tau
          (by simpa [gammaM, rho] using htheta_tau) hgram hmargin
  have hR0 : 0 <= frobNorm R := frobNorm_nonneg R
  have hRI0 : 0 <= frobNorm Rinv := frobNorm_nonneg Rinv
  have hinner0 : 0 <= frobNorm R + theta * frobNorm R :=
    add_nonneg hR0 (mul_nonneg htheta hR0)
  have houter0 : 0 <= frobNorm R + frobNorm Rinv * frobNorm R *
      (frobNorm R + theta * frobNorm R) :=
    add_nonneg hR0 (mul_nonneg (mul_nonneg hRI0 hR0) hinner0)
  have hM : M <= MU := by
    have hIR : frobNorm Rinv * frobNorm R <= BI * BR :=
      mul_le_mul hRI hR hR0 hBI0
    have hinner : frobNorm R + theta * frobNorm R <= BR + tau * BR :=
      add_le_add hR (mul_le_mul htheta_tau' hR hR0 htau)
    have hprod : frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R) <=
        BI * BR * (BR + tau * BR) :=
      mul_le_mul hIR hinner hinner0 (mul_nonneg hBI0 hBR0)
    have houter : frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R) <=
        BR + BI * BR * (BR + tau * BR) := add_le_add hR hprod
    change frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) <=
      BI * (BR + BI * BR * (BR + tau * BR))
    exact mul_le_mul hRI houter houter0 hBI0
  have hM0 : 0 <= M := by
    dsimp [M]
    exact mul_nonneg hRI0 houter0
  have hMU0 : 0 <= MU := hM0.trans hM
  have hKd0 : 0 <= Kd := mul_nonneg hM0 (vecNorm2_nonneg yhat)
  have hBKd0 : 0 <= BKd := by
    dsimp [BKd, higham21SNEQUniformKd]
    exact mul_nonneg hMU0 hBY0
  have hKd : Kd <= BKd := by
    dsimp [Kd, BKd, higham21SNEQUniformKd]
    exact mul_le_mul hM hY (vecNorm2_nonneg yhat) hMU0
  constructor
  . simpa [Kd, BKd] using hKd
  . have hR2 : frobNorm R ^ 2 <= BR ^ 2 :=
      (sq_le_sq₀ hR0 hBR0).mpr hR
    have hRI2 : frobNorm Rinv * frobNorm R ^ 2 <= BI * BR ^ 2 :=
      mul_le_mul hRI hR2 (sq_nonneg (frobNorm R)) hBI0
    have hsum : vecNorm2 yhat + Kd <= BY + BKd := add_le_add hY hKd
    have hmiddle : frobNorm Rinv * frobNorm R ^ 2 *
        (vecNorm2 yhat + Kd) <= BI * BR ^ 2 * (BY + BKd) :=
      mul_le_mul hRI2 hsum
        (add_nonneg (vecNorm2_nonneg yhat) hKd0)
        (mul_nonneg hBI0 (sq_nonneg BR))
    change Crem <= higham21SNEQUniformSignedRemainder A b tau
    dsimp [Crem, higham21SNEQUniformSignedRemainder, BR, BI, BY, BKd]
    exact add_le_add
      (add_le_add
        (mul_le_mul hR hKd hKd0 hBR0)
        hmiddle)
      (mul_le_mul_of_nonneg_left hKd (frobNorm_nonneg A))









































































/-- Fixed-radius second-order bound for the actual rounded Householder-SNE
output relative to its exact nearby QR reference.  Its quadratic coefficient
contains no active factor, direction, rounded vector, or nearby condition
quantity. -/
theorem higham21_sne_householder_actual_output_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (htau_lt : tau < 1)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2) :
    let theta := gamma fp m + higham21SNEHouseholderRho fp m k
    let xhat := higham21SNEActualOutput fp m (m + k) A
      (higham21SNEHouseholderRHat fp A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let qA := higham21SNEQUniformSourceQuantity A b
    vecNorm2 (fun j => xhat j - xbar j) <=
      (gamma fp m * ((m : Real) + Real.sqrt (m : Real)) +
          higham21SNEHouseholderRho fp m k + gamma fp m) * qA +
        theta ^ 2 * higham21SNEQUniformActualCoefficient A b tau := by
  dsimp only
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let qA := higham21SNEQUniformSourceQuantity A b
  let Kc := higham21SNEQUniformConditionTransferCoefficient A b tau
  let qU := higham21SNEQUniformNearbyQuantityBound A b tau
  let Kd := frobNorm Rinv *
    (frobNorm R + frobNorm Rinv * frobNorm R *
      (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
  let Crem := frobNorm R * Kd +
    frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
    frobNorm A * Kd
  let BKd := higham21SNEQUniformKd A b tau
  let Brem := higham21SNEQUniformSignedRemainder A b tau
  let c := (m : Real) + Real.sqrt (m : Real) + 2
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have hrho : 0 <= rho := hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hgamma_theta : gammaM <= theta := by dsimp [theta]; linarith
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have htheta_tau' : theta <= tau := by simpa [theta, gammaM, rho] using htheta_tau
  have htau : 0 <= tau := htheta.trans htheta_tau'
  have hrho_tau : rho <= tau := hrho_theta.trans htheta_tau'
  have hrho_lt : rho < 1 := hrho_tau.trans_lt htau_lt
  have hqA : 0 <= qA := by
    dsimp [qA, higham21SNEQUniformSourceQuantity]
    exact mul_nonneg
      (higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A))
      (vecNorm2_nonneg _)
  have hqB : 0 <= qB := by
    dsimp [qB]
    exact mul_nonneg
      (higham21Cond2With_nonneg B (undetAplusOfGramNonsingInv B))
      (vecNorm2_nonneg xbar)
  have hKc : 0 <= Kc := by
    simpa [Kc] using
      (higham21_sne_q_uniform_coefficient_nonneg A b tau htau hgram).2.2.2
  have hqTransfer : qB <= qA + rho * Kc := by
    have h := (higham21_sne_householder_reference_transfers_q_uniform
      fp A b hm hvalidQR hdiag hdet hrho_pos tau htau
        (by simpa [rho] using hrho_tau) hgram).2.2
    simpa [rho, F, B, xbar, qB, qA, Kc,
      higham21SNEQUniformSourceQuantity] using h
  have hqTheta : qB <= qA + theta * Kc :=
    hqTransfer.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hrho_theta hKc))
  have hqU : qB <= qU := by
    calc
      qB <= qA + rho * Kc := hqTransfer
      _ <= qA + tau * Kc :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hrho_tau hKc)
      _ = qU := rfl
  have hqU0 : 0 <= qU := hqB.trans hqU
  have hcoeff := higham21_sne_householder_actual_coefficients_le_q_uniform
    fp A b hm hvalidQR hmGamma hdiag hdet hrho_pos tau htheta_tau
      hgram hmargin
  have hKd : Kd <= BKd := by
    simpa [gammaM, rho, theta, R, Rinv, yhat, Kd, BKd] using hcoeff.1
  have hCrem : Crem <= Brem := by
    simpa [gammaM, rho, theta, R, Rinv, yhat, Kd, Crem, Brem] using hcoeff.2
  have hc0 : 0 <= c := by
    dsimp [c]
    positivity
  have ha : gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM <=
      theta * c := by
    have hs0 : 0 <= (m : Real) + Real.sqrt (m : Real) := by positivity
    have hrhos : 0 <= rho *
        ((m : Real) + Real.sqrt (m : Real) + 1) := by positivity
    dsimp [theta, c]
    nlinarith
  have hL0 : 0 <=
      gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM := by
    positivity
  have hLrho :
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * rho <=
        theta ^ 2 * c := by
    calc
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * rho <=
          (theta * c) * theta :=
        mul_le_mul ha hrho_theta hrho (mul_nonneg htheta hc0)
      _ = theta ^ 2 * c := by ring
  have hfirst :
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qB <=
        (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
          theta ^ 2 * (c * Kc) := by
    calc
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qB <=
          (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) *
            (qA + rho * Kc) :=
        mul_le_mul_of_nonneg_left hqTransfer hL0
      _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
          ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) *
            rho) * Kc := by ring
      _ <= (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
          (theta ^ 2 * c) * Kc :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hLrho hKc)
      _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
          theta ^ 2 * (c * Kc) := by ring
  have hdenRho : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hdenTau : 0 < 1 - tau := sub_pos.mpr htau_lt
  have hqDiv : qB / (1 - rho) <= qU / (1 - tau) := by
    calc
      qB / (1 - rho) <= qU / (1 - rho) :=
        div_le_div_of_nonneg_right hqU hdenRho.le
      _ <= qU / (1 - tau) :=
        div_le_div_of_nonneg_left hqU0 hdenTau (by linarith)
  have hbracket :
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem <=
        2 * (qU / (1 - tau)) + frobNorm A * BKd + Brem := by
    exact add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left hqDiv (by norm_num))
        (mul_le_mul_of_nonneg_left hKd (frobNorm_nonneg A)))
      hCrem
  have hbase := higham21_sne_householder_actual_output_uniform_quadratic_bound
    fp A b hm hvalidQR hmGamma hdiag hrho_lt
  change vecNorm2 (fun j => xhat j - xbar j) <=
    (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
      theta ^ 2 * higham21SNEQUniformActualCoefficient A b tau
  calc
    vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qB +
        theta ^ 2 *
          (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) := by
      simpa [gammaM, rho, theta, F, B, R, Rinv, yhat, xhat, xbar,
        qB, Kd, Crem] using hbase
    _ <= ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) *
          qA + theta ^ 2 * (c * Kc)) +
        theta ^ 2 *
          (2 * (qU / (1 - tau)) + frobNorm A * BKd + Brem) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hbracket (sq_nonneg theta))
    _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
        theta ^ 2 * higham21SNEQUniformActualCoefficient A b tau := by
      dsimp [higham21SNEQUniformActualCoefficient, Kc, qU, BKd, Brem, c]
      ring

/-- Fixed-radius equation-(21.11) bound for the exact Householder QR
reference, with a direction-independent quadratic coefficient. -/
theorem higham21_sne_householder_reference_output_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (hrho_tau : higham21SNEHouseholderRho fp m k <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => xbar j - x j) <=
      rho * higham21SNEQUniformSourceQuantity A b +
        eta ^ 2 * higham21SNEQUniformReferenceCoefficient A b tau := by
  dsimp only
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let y := rectMatMulVec (undetGramNonsingInv A) b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let Ky := higham21SNEQUniformInverseDifferenceCoefficient A tau * vecNorm2 b
  let Kx := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau *
    vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let CQR := higham21SNEQUniformReferenceCoefficient A b tau
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := hrho_pos.le
  have htau : 0 <= tau := hrho.trans (by simpa [rho] using hrho_tau)
  have hcoeff := higham21_sne_q_uniform_coefficient_nonneg A b tau htau hgram
  have hKy : 0 <= Ky := by
    dsimp [Ky]
    exact mul_nonneg hcoeff.1 (vecNorm2_nonneg b)
  have hKx : 0 <= Kx := by
    dsimp [Kx]
    exact mul_nonneg hcoeff.2.1 (vecNorm2_nonneg b)
  have hnreal : 0 <= (m + k : Real) := by positivity
  have hKyEta : 0 <= KyEta := mul_nonneg hnreal hKy
  have hKxEta : 0 <= KxEta := mul_nonneg hnreal hKx
  have hrho_eta : rho = (m + k : Real) * eta := by
    simp [rho, eta, higham21SNEHouseholderRho]
  have htrans := higham21_sne_householder_reference_transfers_q_uniform
    fp A b hm hvalidQR hdiag hdet hrho_pos tau htau hrho_tau hgram
  have hyRho : vecNorm2 (fun i => ybar i - y i) <= rho * Ky := by
    simpa [rho, F, y, ybar, Ky] using htrans.1
  have hxRho : vecNorm2 (fun j => xbar j - x j) <= rho * Kx := by
    simpa [rho, F, x, xbar, Kx, Aplus] using htrans.2.1
  have hyEta : vecNorm2 (fun i => ybar i - y i) <= eta * KyEta := by
    calc
      vecNorm2 (fun i => ybar i - y i) <= rho * Ky := hyRho
      _ = eta * KyEta := by rw [hrho_eta]; simp [KyEta]; ring
  have hxEta : vecNorm2 (fun j => xbar j - x j) <= eta * KxEta := by
    calc
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx := hxRho
      _ = eta * KxEta := by rw [hrho_eta]; simp [KxEta]; ring
  have hyExact : y = rectTransposeMulVec Aplus x := by
    simpa [y, Aplus, x] using
      higham21_sne_exact_dual_eq_pseudoinverse_transpose A b hdet
  have hF : frobNorm F <= eta * frobNorm A := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_frobNorm fp A hm hvalidQR
  have hrem : vecNorm2
      (higham21Eq21_11FiniteRemainder A F b xbar ybar) <= eta ^ 2 * CQR := by
    have hfinite := higham21_eq21_11_finite_remainder_vecNorm2_le_radius
      eta (frobNorm A) KyEta KxEta heta (frobNorm_nonneg A)
        hKyEta hKxEta A F b xbar ybar hF
        (by
          dsimp only
          rw [<- hyExact]
          exact hyEta)
        (by simpa [Aplus, x] using hxEta)
    simpa [CQR, higham21SNEQUniformReferenceCoefficient, KyEta, KxEta,
      Ky, Kx, Aplus] using hfinite
  have href := higham21_sne_householder_reference_forward_error
    fp A b hm hn hvalidQR hdiag hdet CQR
      (by simpa [F, eta, ybar, xbar] using hrem)
  change vecNorm2 (fun j => xbar j - x j) <=
    rho * higham21SNEQUniformSourceQuantity A b + eta ^ 2 * CQR
  calc
    vecNorm2 (fun j => xbar j - x j) <=
      (m + k : Real) * eta *
          higham21Cond2With A Aplus * vecNorm2 x + eta ^ 2 * CQR := by
      simpa [eta, x, xbar, Aplus] using href
    _ = rho * higham21SNEQUniformSourceQuantity A b + eta ^ 2 * CQR := by
      rw [hrho_eta]
      simp [higham21SNEQUniformSourceQuantity, Aplus, x]
      ring

/-- Fully assembled fixed-radius absolute forward bound for the actual
Householder-SNE output and the canonical exact minimum-norm solution. -/
theorem higham21_sne_householder_actual_output_source_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (htau_lt : tau < 1)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let R := higham21SNEHouseholderRHat fp A
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let qA := higham21SNEQUniformSourceQuantity A b
    vecNorm2 (fun j => xhat j - x j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * qA +
        theta ^ 2 * higham21SNEQUniformSecondOrderCoefficient A b tau := by
  dsimp only
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let R := higham21SNEHouseholderRHat fp A
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let qA := higham21SNEQUniformSourceQuantity A b
  let CA := higham21SNEQUniformActualCoefficient A b tau
  let CR := higham21SNEQUniformReferenceCoefficient A b tau
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have htheta_tau' : theta <= tau := by simpa [theta, gammaM, rho] using htheta_tau
  have htau : 0 <= tau := htheta.trans htheta_tau'
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have hrho_tau : rho <= tau := hrho_theta.trans htheta_tau'
  have hn_one : (1 : Real) <= (m + k : Real) := by
    exact_mod_cast Nat.succ_le_iff.mpr (lt_of_lt_of_le hm (Nat.le_add_right m k))
  have heta_rho : eta <= rho := by
    calc
      eta = 1 * eta := by ring
      _ <= (m + k : Real) * eta := mul_le_mul_of_nonneg_right hn_one heta
      _ = rho := by simp [rho, eta, higham21SNEHouseholderRho]
  have heta_theta : eta <= theta := heta_rho.trans hrho_theta
  have hcoeff := higham21_sne_q_uniform_coefficient_nonneg A b tau htau hgram
  have hCR : 0 <= CR := by
    let Ky := higham21SNEQUniformInverseDifferenceCoefficient A tau * vecNorm2 b
    let Kx := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau *
      vecNorm2 b
    have hKy : 0 <= Ky := mul_nonneg hcoeff.1 (vecNorm2_nonneg b)
    have hKx : 0 <= Kx := mul_nonneg hcoeff.2.1 (vecNorm2_nonneg b)
    have hn0 : 0 <= ((m + k : Nat) : Real) := by
      exact_mod_cast Nat.zero_le (m + k)
    dsimp [CR, higham21SNEQUniformReferenceCoefficient]
    exact mul_nonneg (frobNorm_nonneg A)
      (add_nonneg
        (mul_nonneg
          (add_nonneg (by norm_num)
            (mul_nonneg
              (frobNorm_nonneg (undetAplusOfGramNonsingInv A))
              (frobNorm_nonneg A)))
          (mul_nonneg hn0 hKy))
        (mul_nonneg (frobNorm_nonneg (undetAplusOfGramNonsingInv A))
          (mul_nonneg hn0 hKx)))
  have hActual := higham21_sne_householder_actual_output_q_uniform
    fp A b hm hvalidQR hmGamma hdiag hdet hrho_pos tau htheta_tau
      htau_lt hgram hmargin
  have hReference := higham21_sne_householder_reference_output_q_uniform
    fp A b hm hn hvalidQR hdiag hdet hrho_pos tau
      (by simpa [rho] using hrho_tau) hgram
  have hA : vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * qA +
        theta ^ 2 * CA := by
    simpa [gammaM, rho, theta, R, xhat, xbar, qA, CA] using hActual
  have hR : vecNorm2 (fun j => xbar j - x j) <=
      rho * qA + eta ^ 2 * CR := by
    simpa [eta, rho, x, xbar, qA, CR] using hReference
  have hetaSq : eta ^ 2 <= theta ^ 2 :=
    (sq_le_sq₀ heta htheta).mpr heta_theta
  have hRSquare : eta ^ 2 * CR <= theta ^ 2 * CR :=
    mul_le_mul_of_nonneg_right hetaSq hCR
  change vecNorm2 (fun j => xhat j - x j) <=
    (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * qA +
      theta ^ 2 * higham21SNEQUniformSecondOrderCoefficient A b tau
  calc
    vecNorm2 (fun j => xhat j - x j) =
        vecNorm2 (fun j => (xhat j - xbar j) + (xbar j - x j)) := by
      congr 1
      funext j
      ring
    _ <= vecNorm2 (fun j => xhat j - xbar j) +
        vecNorm2 (fun j => xbar j - x j) := vecNorm2_add_le _ _
    _ <= ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) *
          qA + theta ^ 2 * CA) + (rho * qA + eta ^ 2 * CR) :=
      add_le_add hA hR
    _ <= ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) *
          qA + theta ^ 2 * CA) + (rho * qA + theta ^ 2 * CR) :=
      add_le_add le_rfl (add_le_add le_rfl hRSquare)
    _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          qA + theta ^ 2 * higham21SNEQUniformSecondOrderCoefficient A b tau := by
      dsimp [higham21SNEQUniformSecondOrderCoefficient, CA, CR]
      ring









/-- Final fixed-radius relative forward theorem for the actual rounded
Householder-SNE output.  The coefficient of `theta^2` depends only on
`A`, `b`, the dimensions, and the chosen radius `tau`. -/
theorem higham21_sne_householder_actual_output_source_relative_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k) (hb : b ≠ 0)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (htau_lt : tau < 1)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let R := higham21SNEHouseholderRHat fp A
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        theta ^ 2 *
          higham21SNEQUniformRelativeSecondOrderCoefficient A b tau := by
  dsimp only
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let R := higham21SNEHouseholderRHat fp A
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let C := higham21SNEQUniformSecondOrderCoefficient A b tau
  let lead := gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM
  have hbound : vecNorm2 (fun j => xhat j - x j) <=
      lead * (higham21Cond2With A Aplus * vecNorm2 x) + theta ^ 2 * C := by
    simpa [gammaM, rho, theta, R, xhat, x, Aplus, C, lead,
      higham21SNEQUniformSourceQuantity] using
      higham21_sne_householder_actual_output_source_q_uniform
        fp A b hm hn hvalidQR hmGamma hdiag hdet hrho_pos tau
          htheta_tau htau_lt hgram hmargin
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hAx : rectMatMulVec A x = b := by
    calc
      rectMatMulVec A x = rectMatMulVec (rectMatMul A Aplus) b := by
        simpa [x] using (rectMatMulVec_rectMatMul A Aplus b).symm
      _ = rectMatMulVec (idMatrix m) b := by rw [hRight]
      _ = b := rectMatMulVec_idMatrix b
  have hxne : x ≠ 0 := by
    intro hx0
    apply hb
    calc
      b = rectMatMulVec A x := hAx.symm
      _ = 0 := by
        rw [hx0]
        funext i
        simp [rectMatMulVec]
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hx0
    apply hxne
    funext j
    exact (vecNorm2_eq_zero_iff x).mp hx0 j
  have hxpos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  change vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
    lead * higham21Cond2With A Aplus +
      theta ^ 2 * (C / vecNorm2 x)
  apply (div_le_iff₀ hxpos).2
  calc
    vecNorm2 (fun j => xhat j - x j) <=
        lead * (higham21Cond2With A Aplus * vecNorm2 x) + theta ^ 2 * C :=
      hbound
    _ = (lead * higham21Cond2With A Aplus +
          theta ^ 2 * (C / vecNorm2 x)) * vecNorm2 x := by
      field_simp [ne_of_gt hxpos]

















/-- Literal pointwise `O(u^2)` form of the final Householder-SNE relative
forward theorem.  The established gamma-form first-order lead is preserved;
only the fixed-radius quadratic remainder is converted to `fp.u^2`. -/
theorem higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k) (hb : b ≠ 0)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real)
    (htheta_tau :
      gamma fp m + higham21SNEHouseholderRho fp m k <= tau)
    (htau_lt : tau < 1)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hmargin : tau * higham21SNEQUniformSolveMultiplier A tau <= 1 / 2)
    (hm_half : (m : Real) * fp.u <= 1 / 2)
    (hqr_half :
      ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real) *
        fp.u <= 1 / 2) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let R := higham21SNEHouseholderRHat fp A
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        fp.u ^ 2 *
          higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau := by
  dsimp only
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let R := higham21SNEHouseholderRHat fp A
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let Crel := higham21SNEQUniformRelativeSecondOrderCoefficient A b tau
  let TU := higham21SNEHouseholderThetaUnitRoundoffCoefficient m k
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hgammaU : gammaM <= 2 * ((m : Real) * fp.u) := by
    simpa [gammaM] using gamma_le_two_mul_n_u_of_nu_le_half fp m hm_half
  have hetaU : eta <=
      (2 * ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real)) *
        fp.u := by
    simpa [eta] using
      H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
        fp (m + k) m hqr_half
  have hn0 : 0 <= ((m + k : Nat) : Real) := by positivity
  have hrho_eta : rho = ((m + k : Nat) : Real) * eta := by
    simp [rho, eta, higham21SNEHouseholderRho]
  have hrhoU : rho <=
      2 * (((m + k : Nat) : Real) *
        ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real)) *
          fp.u := by
    calc
      rho = ((m + k : Nat) : Real) * eta := hrho_eta
      _ <= ((m + k : Nat) : Real) *
          ((2 * ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real)) *
            fp.u) := mul_le_mul_of_nonneg_left hetaU hn0
      _ = 2 * (((m + k : Nat) : Real) *
          ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real)) *
            fp.u := by ring
  have hthetaU : theta <= TU * fp.u := by
    calc
      theta = gammaM + rho := rfl
      _ <= 2 * ((m : Real) * fp.u) +
          2 * (((m + k : Nat) : Real) *
            ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real)) *
              fp.u := add_le_add hgammaU hrhoU
      _ = TU * fp.u := by
        dsimp [TU, higham21SNEHouseholderThetaUnitRoundoffCoefficient]
        ring
  have hTU0 : 0 <= TU := by
    dsimp [TU, higham21SNEHouseholderThetaUnitRoundoffCoefficient]
    positivity
  have hTUu0 : 0 <= TU * fp.u := mul_nonneg hTU0 fp.u_nonneg
  have hthetaSq : theta ^ 2 <= (TU * fp.u) ^ 2 :=
    (sq_le_sq₀ htheta hTUu0).mpr hthetaU
  have hrem : theta ^ 2 * Crel <= fp.u ^ 2 *
      higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau := by
    calc
      theta ^ 2 * Crel <= theta ^ 2 * |Crel| :=
        mul_le_mul_of_nonneg_left (le_abs_self Crel) (sq_nonneg theta)
      _ <= (TU * fp.u) ^ 2 * |Crel| :=
        mul_le_mul_of_nonneg_right hthetaSq (abs_nonneg Crel)
      _ = fp.u ^ 2 *
          higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau := by
        dsimp [higham21SNEQUniformUnitRoundoffSecondOrderCoefficient, TU, Crel]
        ring
  have hbase := higham21_sne_householder_actual_output_source_relative_q_uniform
    fp A b hm hn hb hvalidQR hmGamma hdiag hdet hrho_pos tau htheta_tau
      htau_lt hgram hmargin
  change vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
    (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) +
      fp.u ^ 2 * higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau
  calc
    vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        theta ^ 2 * Crel := by
      simpa [gammaM, rho, theta, R, xhat, x, Crel] using hbase
    _ <= (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        fp.u ^ 2 *
          higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau :=
      add_le_add le_rfl hrem

end NumStability
