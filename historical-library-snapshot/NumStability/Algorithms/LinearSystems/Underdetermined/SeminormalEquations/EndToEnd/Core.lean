import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.EndToEnd
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ConditionTransfer.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.EnvelopeTransfer
import NumStability.Source.Higham.Chapter21.Equation11.ActualOutput
import NumStability.Source.Higham.Chapter21.Equation11.Forward
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.EnvelopeTransfer
import NumStability.Source.Higham.Chapter21.Equation11.RemainderBounds
import NumStability.Source.Higham.Chapter21.Equation11.Closure
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Closure

/-!
# Algorithms.Underdetermined.Higham21SNEClosure

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete Householder-QR closure for the seminormal-equations path.







namespace NumStability

open scoped BigOperators

/-!
# Concrete signed SNE closure

The analysis-only QR perturbation below is chosen from the proved
implementation-backed Householder panel theorem.  The computed objects remain
the actual panel `Q`, its actual top square `R_hat`, the two rounded triangular
solves, and the rounded final `A^T` action.
-/






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Direction-radius closure for the concrete Householder perturbation.

The perturbation is normalized by its actual componentwise coefficient
`rho`; the nonnegative source envelope is the proved Householder majorant
`E = G |A|`.
The single smallness hypothesis places that concrete perturbation inside the
determinant-preserving radius from the Chapter 21 perturbation theory.  The
three conclusions are the dual displacement, primal displacement, and full
condition-times-solution transfer used below. -/
theorem higham21_sne_householder_direction_radius_transfers
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let y := rectMatMulVec G b
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kc := higham21SNEConditionTransferCoefficient
      A D b G radius beta
    vecNorm2 (fun i => ybar i - y i) <= rho * Ky /\
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx /\
      higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar <=
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
            vecNorm2 x + rho * Kc := by
  dsimp only at hrho_radius ⊢
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let y := rectMatMulVec G b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kc := higham21SNEConditionTransferCoefficient
    A D b G radius beta
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have hE : forall i j, 0 <= E i j := by
    intro i j
    dsimp [E]
    exact Finset.sum_nonneg (fun s _ =>
      mul_nonneg (higham21_sne_householder_G_nonneg hm j s) (abs_nonneg _))
  have hD : forall i j, |D i j| <= E i j := by
    intro i j
    have hFcomp :=
      higham21_sne_householder_deltaA_componentwise fp A hm hvalidQR j i
    dsimp [D]
    rw [abs_div, abs_of_pos hrho_pos]
    exact (div_le_iff₀ hrho_pos).2 (by
      calc
        |F i j| <= rho * E i j := by
          simpa [F, rho, E] using hFcomp
        _ = E i j * rho := by ring)
  have hscaled : higham21Eq21_7ScaledMatrix A D rho = B := by
    ext i j
    dsimp [higham21Eq21_7ScaledMatrix, D, B]
    rw [mul_div_cancel₀ _ (ne_of_gt hrho_pos)]
  have hyRaw :=
    higham21_sne_dual_solution_difference_vecNorm2_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  have hxRaw :=
    higham21_sne_primal_solution_difference_vecNorm2_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  have hqRaw :=
    higham21_sne_cond2_mul_solution_norm_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  rw [hscaled] at hyRaw
  rw [hscaled] at hxRaw
  rw [hscaled] at hqRaw
  have hybar : ybar = rectMatMulVec (undetGramNonsingInv B) b := by
    simpa [ybar, B, F] using
      higham21_sne_householder_referenceY_eq_nearby_gram_inverse
        fp A b hm hvalidQR hdiag
  have hxbar : xbar =
      rectMatMulVec (undetAplusOfGramNonsingInv B) b := by
    simpa [xbar, B, F] using
      higham21_sne_householder_referenceOutput_eq_nearby_pseudoinverse
        fp A b hm hvalidQR hdiag
  constructor
  . change vecNorm2 (fun i => ybar i - y i) <= rho * Ky
    rw [hybar]
    simpa [G, y, Ky, radius, beta, undetGramNonsingInv,
      matMulVec, rectMatMulVec] using hyRaw
  constructor
  . change vecNorm2 (fun j => xbar j - x j) <= rho * Kx
    rw [hxbar]
    simpa [G, x, Kx, radius, beta, undetAplusOfGramNonsingInv]
      using hxRaw
  . change higham21Cond2With B (undetAplusOfGramNonsingInv B) *
        vecNorm2 xbar <=
      higham21Cond2With A (undetAplusOfGramNonsingInv A) *
        vecNorm2 x + rho * Kc
    rw [hxbar]
    simpa [G, x, Kc, radius, beta, undetAplusOfGramNonsingInv]
      using hqRaw


































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Source-facing form of the fully closed actual-to-reference estimate.

The first-order condition expression is now the original
`cond2(A) * ||A^+ b||`.  The displayed square coefficient is a concrete
finite-roundoff coefficient: it may contain the active nearby quantity
`qB / (1-rho)` and the actual rounded normal solution, but it contains no
assumed error bound, no quotient by the master radius, and no quantity chosen
from the conclusion. -/
theorem higham21_sne_householder_actual_output_source_finite_quadratic_bound
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
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R +
          frobNorm Rinv * frobNorm R *
            (frobNorm R + theta * frobNorm R)) *
        vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 * Cfinite := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R +
        frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) *
      vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let s := (m : Real) + Real.sqrt (m : Real)
  let L := gammaM * s + rho + gammaM
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have hs : 0 <= s := by
    exact add_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg _)
  have hradius : 0 <= radius := by
    exact hrho.trans (by simpa [rho, F, D, E, radius] using hrho_radius)
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21PerturbationGramInverseBound_nonneg A
  have hKc : 0 <= Kc := by
    simpa [Kc] using
      higham21_sne_conditionTransferCoefficient_nonneg
        A D b G radius beta hradius hbeta
  have hqTransfer : qB <= q + rho * Kc := by
    simpa [rho, F, D, E, B, G, radius, beta, x, xbar, q, qB, Kc] using
      (higham21_sne_householder_direction_radius_transfers
        fp A b hm hvalidQR hdiag hdet hrho_pos hrho_radius).2.2
  have hCore : vecNorm2 (fun j => xhat j - xbar j) <=
      L * qB + theta ^ 2 *
        (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) := by
    simpa [gammaM, rho, theta, F, B, R, Rinv, yhat, xhat, xbar,
      qB, Kd, Crem, s, L] using
      higham21_sne_householder_actual_output_uniform_quadratic_bound
        fp A b hm hvalidQR hmGamma hdiag hrho_lt
  have hL : 0 <= L := by
    dsimp [L]
    exact add_nonneg (add_nonneg (mul_nonneg hgamma hs) hrho) hgamma
  have hLtheta : L <= theta * (s + 2) := by
    dsimp [L, theta]
    nlinarith [mul_nonneg hrho hs]
  have hLrho : L * rho <= theta ^ 2 * (s + 2) := by
    calc
      L * rho <= (theta * (s + 2)) * rho :=
        mul_le_mul_of_nonneg_right hLtheta hrho
      _ <= (theta * (s + 2)) * theta :=
        mul_le_mul_of_nonneg_left hrho_theta
          (mul_nonneg htheta (by linarith))
      _ = theta ^ 2 * (s + 2) := by ring
  have hlead : L * qB <= L * q + theta ^ 2 * ((s + 2) * Kc) := by
    calc
      L * qB <= L * (q + rho * Kc) :=
        mul_le_mul_of_nonneg_left hqTransfer hL
      _ = L * q + (L * rho) * Kc := by ring
      _ <= L * q + (theta ^ 2 * (s + 2)) * Kc :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hLrho hKc)
      _ = L * q + theta ^ 2 * ((s + 2) * Kc) := by ring
  calc
    vecNorm2 (fun j => xhat j - xbar j) <=
        L * qB + theta ^ 2 *
          (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) := hCore
    _ <= (L * q + theta ^ 2 * ((s + 2) * Kc)) +
        theta ^ 2 *
          (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) :=
      add_le_add hlead le_rfl
    _ = L * q + theta ^ 2 * Cfinite := by
      simp [Cfinite]
      ring





















































































































/-- Equation (21.11) for the exact QR reference with its finite remainder
closed from the concrete direction-radius transfer.

Unlike the compatibility theorem above, this result has no supplied
remainder premise. -/
theorem higham21_sne_householder_reference_forward_error_closed_direction_radius
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xbar j - x j) <=
      rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR := by
  dsimp only at hrho_radius ⊢
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let y := rectMatMulVec G b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let CQR := frobNorm A *
    ((1 + frobNorm Aplus * frobNorm A) * KyEta +
      frobNorm Aplus * KxEta)
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have hradius : 0 <= radius := by
    exact hrho.trans (by simpa [rho, F, D, E, radius] using hrho_radius)
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21PerturbationGramInverseBound_nonneg A
  have hKy : 0 <= Ky := by
    dsimp [Ky]
    exact mul_nonneg
      (higham21_sne_inverseDifferenceCoefficient_nonneg
        A D G radius beta hradius hbeta)
      (vecNorm2_nonneg b)
  have hKx : 0 <= Kx := by
    dsimp [Kx]
    exact mul_nonneg
      (higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
        A D G radius beta hradius hbeta)
      (vecNorm2_nonneg b)
  have hnreal : 0 <= (m + k : Real) := by positivity
  have hKyEta : 0 <= KyEta := mul_nonneg hnreal hKy
  have hKxEta : 0 <= KxEta := mul_nonneg hnreal hKx
  have hrho_eta : rho = (m + k : Real) * eta := by
    simp [rho, eta, higham21SNEHouseholderRho]
  have htrans := higham21_sne_householder_direction_radius_transfers
    fp A b hm hvalidQR hdiag hdet hrho_pos hrho_radius
  have hyRho : vecNorm2 (fun i => ybar i - y i) <= rho * Ky := by
    simpa [rho, F, D, E, G, radius, beta, y, ybar, Ky] using htrans.1
  have hxRho : vecNorm2 (fun j => xbar j - x j) <= rho * Kx := by
    simpa [rho, F, D, E, G, radius, beta, x, xbar, Kx, Aplus] using
      htrans.2.1
  have hyEta : vecNorm2 (fun i => ybar i - y i) <= eta * KyEta := by
    calc
      vecNorm2 (fun i => ybar i - y i) <= rho * Ky := hyRho
      _ = eta * KyEta := by rw [hrho_eta]; simp [KyEta]; ring
  have hxEta : vecNorm2 (fun j => xbar j - x j) <= eta * KxEta := by
    calc
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx := hxRho
      _ = eta * KxEta := by rw [hrho_eta]; simp [KxEta]; ring
  have hyExact : y = rectTransposeMulVec Aplus x := by
    simpa [y, Aplus, x, G] using
      higham21_sne_exact_dual_eq_pseudoinverse_transpose A b hdet
  have hF : frobNorm F <= eta * frobNorm A := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_frobNorm fp A hm hvalidQR
  have hrem : vecNorm2
      (higham21Eq21_11FiniteRemainder A F b xbar ybar) <=
        eta ^ 2 * CQR := by
    have hfinite := higham21_eq21_11_finite_remainder_vecNorm2_le_radius
      eta (frobNorm A) KyEta KxEta heta (frobNorm_nonneg A)
        hKyEta hKxEta A F b xbar ybar hF
        (by
          dsimp only
          rw [← hyExact]
          exact hyEta)
        (by simpa [Aplus, x] using hxEta)
    simpa [CQR, Aplus] using hfinite
  have href := higham21_sne_householder_reference_forward_error
    fp A b hm hn hvalidQR hdiag hdet CQR
      (by simpa [F, eta, ybar, xbar] using hrem)
  calc
    vecNorm2 (fun j => xbar j - x j) <=
        (m + k : Real) * eta *
            higham21Cond2With A Aplus * vecNorm2 x + eta ^ 2 * CQR := by
      simpa [eta, x, xbar, Aplus] using href
    _ = rho * higham21Cond2With A Aplus * vecNorm2 x +
        eta ^ 2 * CQR := by rw [hrho_eta]

/-- Fully assembled finite-roundoff forward bound for the actual Householder
SNE output and the canonical exact solution of the original system.

Every algorithmic error certificate (QR, both triangular solves, final
formation, condition transfer, and the finite equation-(21.11) remainder) is
instantiated internally. -/
theorem higham21_sne_householder_actual_output_source_forward_finite_bound
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
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xhat j - x j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * q +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let CQR := frobNorm A *
    ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
      frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
  have hactual : vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 * Cfinite := by
    simpa [gammaM, rho, theta, F, D, E, B, G, radius, beta, R, Rinv,
      yhat, xhat, x, xbar, q, qB, Kc, Kd, Crem, Cfinite] using
      higham21_sne_householder_actual_output_source_finite_quadratic_bound
        fp A b hm hvalidQR hmGamma hdiag hdet hrho_pos hrho_lt hrho_radius
  have href : vecNorm2 (fun j => xbar j - x j) <=
      rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR := by
    simpa [eta, rho, F, D, E, G, radius, beta, x, xbar, Ky, Kx,
      KyEta, KxEta, CQR] using
      higham21_sne_householder_reference_forward_error_closed_direction_radius
        fp A b hm hn hvalidQR hdiag hdet hrho_pos hrho_radius
  have hsplit : (fun j => xhat j - x j) =
      fun j => (xhat j - xbar j) + (xbar j - x j) := by
    ext j
    ring
  rw [hsplit]
  calc
    vecNorm2 (fun j => (xhat j - xbar j) + (xbar j - x j)) <=
        vecNorm2 (fun j => xhat j - xbar j) +
          vecNorm2 (fun j => xbar j - x j) := vecNorm2_add_le _ _
    _ <= ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
          theta ^ 2 * Cfinite) +
        (rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR) := add_le_add hactual href
    _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * q +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
      simp [q]
      ring

/-- Higham, 2nd ed., Chapter 21, equation (21.11): source-active relative
forward endpoint for the actual Householder seminormal-equations algorithm.

The right-hand side is nonzero, so the exact minimum-norm solution provides a
valid relative normalization.  The first-order term is entirely in the
original source condition number.  The remaining displayed quotient is an
explicit finite second-order coefficient built from the active QR direction,
the actual rounded normal solution, and fixed-radius perturbation data; it is
not a supplied error certificate. -/
theorem higham21_sne_householder_actual_output_source_forward_relative_finite
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        (theta ^ 2 * Cfinite + eta ^ 2 * CQR) / vecNorm2 x := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let CQR := frobNorm A *
    ((1 + frobNorm Aplus * frobNorm A) * KyEta + frobNorm Aplus * KxEta)
  let lead := gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM
  have hbound : vecNorm2 (fun j => xhat j - x j) <=
      lead * (higham21Cond2With A Aplus * vecNorm2 x) +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
    simpa [gammaM, eta, rho, theta, F, D, E, B, G, radius, beta,
      R, Rinv, yhat, xhat, x, xbar, qB, Ky, Kx, KyEta, KxEta,
      Kc, Kd, Crem, Cfinite, CQR, lead, Aplus] using
      higham21_sne_householder_actual_output_source_forward_finite_bound
        fp A b hm hn hvalidQR hmGamma hdiag hdet hrho_pos hrho_lt hrho_radius
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
  apply (div_le_iff₀ hxpos).2
  calc
    vecNorm2 (fun j => xhat j - x j) <=
        lead * (higham21Cond2With A Aplus * vecNorm2 x) +
          theta ^ 2 * Cfinite + eta ^ 2 * CQR := hbound
    _ = (lead * higham21Cond2With A Aplus +
          (theta ^ 2 * Cfinite + eta ^ 2 * CQR) / vecNorm2 x) *
        vecNorm2 x := by
      field_simp [ne_of_gt hxpos]
      ring

end NumStability
