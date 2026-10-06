import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.EndToEnd
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.Uniform
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.Signed
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation07.ConditionTransfer
import NumStability.Source.Higham.Chapter21.Equation07.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation11.Uniform
import NumStability.Source.Higham.Chapter21.Equation11.UniformClosure
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Closure

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.Uniform

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
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



































noncomputable def higham21SNEQUniformRBound
    {m n : Nat} (A : Fin m -> Fin n -> Real) (tau : Real) : Real :=
  frobNorm A + tau * higham21SNEQUniformDirectionFrob A

noncomputable def higham21SNEQUniformRInvBound
    {m n : Nat} (A : Fin m -> Fin n -> Real) (tau : Real) : Real :=
  higham21SNEQUniformBeta A tau * higham21SNEQUniformRBound A tau

noncomputable def higham21SNEQUniformSolveMultiplier
    {m n : Nat} (A : Fin m -> Fin n -> Real) (tau : Real) : Real :=
  let BR := higham21SNEQUniformRBound A tau
  let BI := higham21SNEQUniformRInvBound A tau
  BI * (BR + BI * BR * (BR + tau * BR))

noncomputable def higham21SNEQUniformYHatBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  2 * higham21SNEQUniformBeta A tau * vecNorm2 b

noncomputable def higham21SNEQUniformKd
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  higham21SNEQUniformSolveMultiplier A tau *
    higham21SNEQUniformYHatBound A b tau

noncomputable def higham21SNEQUniformSignedRemainder
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  let BR := higham21SNEQUniformRBound A tau
  let BI := higham21SNEQUniformRInvBound A tau
  let BY := higham21SNEQUniformYHatBound A b tau
  let BKd := higham21SNEQUniformKd A b tau
  BR * BKd + BI * BR ^ 2 * (BY + BKd) + frobNorm A * BKd







noncomputable def higham21SNEQUniformNearbyQuantityBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  higham21SNEQUniformSourceQuantity A b +
    tau * higham21SNEQUniformConditionTransferCoefficient A b tau

noncomputable def higham21SNEQUniformActualCoefficient
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  let Kc := higham21SNEQUniformConditionTransferCoefficient A b tau
  let qB := higham21SNEQUniformNearbyQuantityBound A b tau
  let BKd := higham21SNEQUniformKd A b tau
  let Brem := higham21SNEQUniformSignedRemainder A b tau
  ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
    2 * (qB / (1 - tau)) + frobNorm A * BKd + Brem

noncomputable def higham21SNEQUniformReferenceCoefficient
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  let Ky := higham21SNEQUniformInverseDifferenceCoefficient A tau * vecNorm2 b
  let Kx :=
    higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau * vecNorm2 b
  frobNorm A *
    ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) *
        ((n : Real) * Ky) +
      frobNorm (undetAplusOfGramNonsingInv A) * ((n : Real) * Kx))

noncomputable def higham21SNEQUniformSecondOrderCoefficient
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  higham21SNEQUniformActualCoefficient A b tau +
    higham21SNEQUniformReferenceCoefficient A b tau










/-- The normalized concrete Householder perturbation lies in the fixed source
envelope. -/
theorem higham21_sne_householder_normalized_direction_le_sourceEnvelope
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    forall i j, |D i j| <= higham21SNEHouseholderSourceEnvelope A i j := by
  dsimp only
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  intro i j
  have hF := higham21_sne_householder_deltaA_componentwise
    fp A hm hvalidQR j i
  rw [abs_div, abs_of_pos hrho_pos]
  apply (div_le_iff₀ hrho_pos).2
  calc
    |F i j| <= rho * higham21SNEHouseholderSourceEnvelope A i j := by
      simpa [F, rho, higham21SNEHouseholderSourceEnvelope] using hF
    _ = higham21SNEHouseholderSourceEnvelope A i j * rho := by ring

/-- The normalized Householder direction satisfies the rowwise normalization
used by the existing uniform Q-method neighborhood. -/
theorem higham21_sne_householder_normalized_direction_rowNorm_le
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    forall i, rectRowNorm2 D i <= rectRowNorm2 A i := by
  dsimp only
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  have hn_one : (1 : Real) <= (m + k : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have heta_rho : eta <= rho := by
    calc
      eta = (1 : Real) * eta := by ring
      _ <= (m + k : Real) * eta :=
        mul_le_mul_of_nonneg_right hn_one heta
      _ = rho := by simp [rho, eta, higham21SNEHouseholderRho]
  have hrho_inv : 0 <= rho⁻¹ := inv_nonneg.mpr hrho_pos.le
  have hratio : rho⁻¹ * eta <= 1 := by
    have hdiv : eta / rho <= 1 := (div_le_iff₀ hrho_pos).2 (by simpa using heta_rho)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  intro i
  have hFrow : rectRowNorm2 F i <= eta * rectRowNorm2 A i := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_rowwise fp A hm hvalidQR i
  have hDrow : rectRowNorm2 D i = rho⁻¹ * rectRowNorm2 F i := by
    calc
      rectRowNorm2 D i =
          vecNorm2 (fun j : Fin (m + k) => rho⁻¹ * F i j) := by
        unfold rectRowNorm2
        congr 1
        funext j
        simp [D, div_eq_mul_inv, mul_comm]
      _ = |rho⁻¹| * rectRowNorm2 F i :=
        vecNorm2_smul rho⁻¹ (fun j : Fin (m + k) => F i j)
      _ = rho⁻¹ * rectRowNorm2 F i := by
        rw [abs_of_pos (inv_pos.mpr hrho_pos)]
  rw [hDrow]
  calc
    rho⁻¹ * rectRowNorm2 F i <= rho⁻¹ * (eta * rectRowNorm2 A i) :=
      mul_le_mul_of_nonneg_left hFrow hrho_inv
    _ = (rho⁻¹ * eta) * rectRowNorm2 A i := by ring
    _ <= 1 * rectRowNorm2 A i :=
      mul_le_mul_of_nonneg_right hratio (rectRowNorm2_nonneg A i)
    _ = rectRowNorm2 A i := one_mul _















































/-- A row-normalized direction has the public direction-independent
Frobenius bound used by the Q-method neighborhood. -/
theorem higham21_sne_direction_frobNorm_le_q_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNorm D <= higham21SNEQUniformDirectionFrob A := by
  have hrowA : forall i, rectRowNorm2 A i <= frobNorm A := by
    intro i
    have hrect : rectRowNorm2 A i <= frobNormRect A := by
      unfold rectRowNorm2 vecNorm2 frobNormRect
      apply Real.sqrt_le_sqrt
      simpa [frobNormSqRect, vecNorm2Sq] using
        (vecNorm2Sq_row_le_frobNormSq A i)
    simpa [frobNormRect_eq_frobNormFn] using hrect
  have hentry : forall i j, |D i j| <= frobNorm A := by
    intro i j
    calc
      |D i j| <= rectRowNorm2 D i := by
        simpa [rectRowNorm2] using
          (abs_coord_le_vecNorm2 (fun q : Fin n => D i q) j)
      _ <= rectRowNorm2 A i := hrow i
      _ <= frobNorm A := hrowA i
  have hrect := frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
    D (frobNorm_nonneg A) hentry
  simpa [higham21SNEQUniformDirectionFrob,
    higham21Eq21_11UniformDirectionFrobBound,
    frobNormRect_eq_frobNormFn] using hrect

/-- The fixed Q-neighborhood Gram-inverse envelope is nonnegative under its
strict contraction hypothesis. -/
theorem higham21_sne_q_uniform_beta_nonneg
    {m n : Nat} (A : Fin m -> Fin n -> Real) (tau : Real)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    0 <= higham21SNEQUniformBeta A tau := by
  let c := higham21Eq21_11UniformGramContraction A tau
  have hden : 0 < 1 - c := sub_pos.mpr (by simpa [c] using hgram)
  dsimp [higham21SNEQUniformBeta,
    higham21Eq21_11UniformGramInverseBound]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le m) (one_div_pos.mpr hden).le)
      (infNorm_nonneg _))

/-- Public coefficient-domination form of the private calculation used by the
uniform equation-(21.11) theorem. -/
theorem higham21_sne_inverseDifferenceCoefficient_le_q_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (tau : Real)
    (htau : 0 <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i) :
    higham21Eq21_7InverseDifferenceCoefficient A D
        (undetGramNonsingInv A) tau (higham21SNEQUniformBeta A tau) <=
      higham21SNEQUniformInverseDifferenceCoefficient A tau := by
  let G := undetGramNonsingInv A
  let H := higham21Eq21_7GramLinear A D
  let K := higham21Eq21_7GramQuadratic D
  let LH := higham21Eq21_7LinearizedMatrix G H
  let LK := higham21Eq21_7LinearizedMatrix G K
  let Ebar := higham21Eq21_7GramAbsEnvelope A D tau
  let P := ch7InverseFirstProductSensitivity m G Ebar
  let beta := higham21SNEQUniformBeta A tau
  let d := higham21SNEQUniformDirectionFrob A
  have hd : 0 <= d := by
    dsimp [d, higham21SNEQUniformDirectionFrob,
      higham21Eq21_11UniformDirectionFrobBound]
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)
  have hbeta : 0 <= beta := by
    let c := higham21Eq21_11UniformGramContraction A tau
    have hden : 0 < 1 - c := sub_pos.mpr (by simpa [c] using hgram)
    dsimp [beta, higham21SNEQUniformBeta,
      higham21Eq21_11UniformGramInverseBound]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg
        (mul_nonneg (by exact_mod_cast Nat.zero_le m) (one_div_pos.mpr hden).le)
        (infNorm_nonneg _))
  have hD : frobNorm D <= d := by
    simpa [d] using higham21_sne_direction_frobNorm_le_q_uniform A D hrow
  have hH : frobNorm H <= higham21Eq21_11UniformGramLinearFrobBound A := by
    have hprod : H = fun i r =>
        rectMatMul A (finiteTranspose D) i r +
          rectMatMul D (finiteTranspose A) i r := by
      ext i r
      simp only [H, higham21Eq21_7GramLinear, rectMatMul, finiteTranspose]
      rw [Finset.sum_add_distrib]
    have hDT : frobNorm (finiteTranspose D) = frobNorm D := by
      rw [<- frobNormRect_eq_frobNormFn, frobNormRect_finiteTranspose,
        frobNormRect_eq_frobNormFn]
    have hAT : frobNorm (finiteTranspose A) = frobNorm A := by
      rw [<- frobNormRect_eq_frobNormFn, frobNormRect_finiteTranspose,
        frobNormRect_eq_frobNormFn]
    rw [hprod]
    calc
      frobNorm (fun i r =>
          rectMatMul A (finiteTranspose D) i r +
            rectMatMul D (finiteTranspose A) i r) <=
        frobNorm (rectMatMul A (finiteTranspose D)) +
          frobNorm (rectMatMul D (finiteTranspose A)) := frobNorm_add_le _ _
      _ <= frobNorm A * frobNorm D + frobNorm D * frobNorm A :=
        add_le_add
          (by simpa [frobNormRect_eq_frobNormFn, hDT] using
            (frobNormRect_rectMatMul_le A (finiteTranspose D)))
          (by simpa [frobNormRect_eq_frobNormFn, hAT] using
            (frobNormRect_rectMatMul_le D (finiteTranspose A)))
      _ = 2 * frobNorm A * frobNorm D := by ring
      _ <= 2 * frobNorm A * d :=
        mul_le_mul_of_nonneg_left hD
          (mul_nonneg (by norm_num) (frobNorm_nonneg A))
      _ = higham21Eq21_11UniformGramLinearFrobBound A := by
        simp [higham21Eq21_11UniformGramLinearFrobBound,
          d, higham21SNEQUniformDirectionFrob,
          frobNormRect_eq_frobNormFn]
  have hK : frobNorm K <=
      higham21Eq21_11UniformGramQuadraticFrobBound A := by
    have hprod : K = rectMatMul D (finiteTranspose D) := by
      ext i j
      rfl
    have hDT : frobNorm (finiteTranspose D) = frobNorm D := by
      rw [<- frobNormRect_eq_frobNormFn, frobNormRect_finiteTranspose,
        frobNormRect_eq_frobNormFn]
    rw [hprod]
    calc
      frobNorm (rectMatMul D (finiteTranspose D)) <=
          frobNorm D * frobNorm D := by
        simpa [frobNormRect_eq_frobNormFn, hDT] using
          (frobNormRect_rectMatMul_le D (finiteTranspose D))
      _ <= d * d := mul_le_mul hD hD (frobNorm_nonneg D) hd
      _ = higham21Eq21_11UniformGramQuadraticFrobBound A := by
        simp [higham21Eq21_11UniformGramQuadraticFrobBound,
          d, higham21SNEQUniformDirectionFrob, pow_two]
  have hlinearized : forall (M : Fin m -> Fin m -> Real) (s : Real),
      frobNorm M <= s ->
      frobNorm (higham21Eq21_7LinearizedMatrix G M) <= frobNorm G ^ 2 * s := by
    intro M s hM
    have heq : higham21Eq21_7LinearizedMatrix G M =
        matMul m (matMul m G M) G := by
      ext i j
      exact ch7InverseLinearizedEntry_eq_matMul m G M i j
    rw [heq]
    calc
      frobNorm (matMul m (matMul m G M) G) <=
          frobNorm (matMul m G M) * frobNorm G :=
        frobNorm_matMul_le (matMul m G M) G
      _ <= (frobNorm G * frobNorm M) * frobNorm G :=
        mul_le_mul_of_nonneg_right (frobNorm_matMul_le G M) (frobNorm_nonneg G)
      _ <= (frobNorm G * s) * frobNorm G :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM (frobNorm_nonneg G))
          (frobNorm_nonneg G)
      _ = frobNorm G ^ 2 * s := by ring
  have hLH : frobNorm LH <=
      higham21Eq21_11UniformLinearizedLinearBound A := by
    simpa [LH, G, higham21Eq21_11UniformLinearizedLinearBound] using
      hlinearized H (higham21Eq21_11UniformGramLinearFrobBound A) hH
  have hLK : frobNorm LK <=
      higham21Eq21_11UniformLinearizedQuadraticBound A := by
    simpa [LK, G, higham21Eq21_11UniformLinearizedQuadraticBound] using
      hlinearized K (higham21Eq21_11UniformGramQuadraticFrobBound A) hK
  have hEbar : frobNorm Ebar <=
      higham21Eq21_11UniformGramAbsFrobBound A tau := by
    change frobNorm (fun i j => |H i j| + tau * |K i j|) <= _
    calc
      frobNorm (fun i j => |H i j| + tau * |K i j|) <=
          frobNorm (absMatrix m H) +
            frobNorm (fun i j => tau * absMatrix m K i j) := by
        simpa [absMatrix] using
          (frobNorm_add_le (absMatrix m H)
            (fun i j => tau * absMatrix m K i j))
      _ = frobNorm H + tau * frobNorm K := by
        rw [show frobNorm (absMatrix m H) = frobNorm H by
          rw [<- frobNormRect_eq_frobNormFn,
            <- frobNormRect_eq_frobNormFn]
          simpa [absMatrix] using frobNormRect_abs H]
        rw [show frobNorm (fun i j => tau * absMatrix m K i j) =
            tau * frobNorm K by
          rw [<- frobNormRect_eq_frobNormFn, frobNormRect_smul,
            abs_of_nonneg htau, frobNormRect_eq_frobNormFn]
          congr 1
          rw [<- frobNormRect_eq_frobNormFn,
            <- frobNormRect_eq_frobNormFn]
          simpa [absMatrix] using frobNormRect_abs K]
      _ <= higham21Eq21_11UniformGramLinearFrobBound A +
          tau * higham21Eq21_11UniformGramQuadraticFrobBound A :=
        add_le_add hH (mul_le_mul_of_nonneg_left hK htau)
      _ = higham21Eq21_11UniformGramAbsFrobBound A tau := rfl
  have hP : frobNorm P <=
      higham21Eq21_11UniformFirstProductFrobBound A tau := by
    calc
      frobNorm P <= frobNorm (absMatrix m G) * frobNorm Ebar := by
        simpa [P, ch7InverseFirstProductSensitivity] using
          frobNorm_matMul_le (absMatrix m G) Ebar
      _ = frobNorm G * frobNorm Ebar := by
        congr 1
        rw [<- frobNormRect_eq_frobNormFn,
          <- frobNormRect_eq_frobNormFn]
        simpa [absMatrix] using frobNormRect_abs G
      _ <= frobNorm G * higham21Eq21_11UniformGramAbsFrobBound A tau :=
        mul_le_mul_of_nonneg_left hEbar (frobNorm_nonneg G)
      _ = higham21Eq21_11UniformFirstProductFrobBound A tau := rfl
  have hFirst0 : 0 <= higham21Eq21_11UniformFirstProductFrobBound A tau := by
    dsimp [higham21Eq21_11UniformFirstProductFrobBound]
    exact mul_nonneg (frobNorm_nonneg G)
      (add_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (frobNormRect_nonneg A)) hd)
        (mul_nonneg htau (sq_nonneg d)))
  have hP2 : frobNorm P ^ 2 <=
      higham21Eq21_11UniformFirstProductFrobBound A tau ^ 2 :=
    (sq_le_sq₀ (frobNorm_nonneg P) hFirst0).mpr hP
  have hIQ : frobNorm P ^ 2 * beta <=
      higham21Eq21_11UniformInverseQuadraticBound A tau := by
    simpa [beta, higham21SNEQUniformBeta,
      higham21Eq21_11UniformInverseQuadraticBound] using
      mul_le_mul_of_nonneg_right hP2 hbeta
  change frobNorm LH + tau * frobNorm LK + tau * (frobNorm P ^ 2 * beta) <= _
  calc
    frobNorm LH + tau * frobNorm LK + tau * (frobNorm P ^ 2 * beta) <=
        higham21Eq21_11UniformLinearizedLinearBound A +
          tau * higham21Eq21_11UniformLinearizedQuadraticBound A +
          tau * higham21Eq21_11UniformInverseQuadraticBound A tau :=
      add_le_add
        (add_le_add hLH (mul_le_mul_of_nonneg_left hLK htau))
        (mul_le_mul_of_nonneg_left hIQ htau)
    _ = higham21SNEQUniformInverseDifferenceCoefficient A tau := rfl

/-- The active pseudoinverse-difference coefficient is dominated by the
source-defined Q-neighborhood coefficient. -/
theorem higham21_sne_pseudoinverseDifferenceCoefficient_le_q_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (tau : Real)
    (htau : 0 <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i) :
    higham21SNEPseudoinverseDifferenceCoefficient A D
        (undetGramNonsingInv A) tau (higham21SNEQUniformBeta A tau) <=
      higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau := by
  let beta := higham21SNEQUniformBeta A tau
  let invC := higham21Eq21_7InverseDifferenceCoefficient A D
    (undetGramNonsingInv A) tau beta
  let invU := higham21SNEQUniformInverseDifferenceCoefficient A tau
  let d := higham21SNEQUniformDirectionFrob A
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hD : frobNorm D <= d := by
    simpa [d] using higham21_sne_direction_frobNorm_le_q_uniform A D hrow
  have hInv : invC <= invU := by
    simpa [invC, invU, beta] using
      higham21_sne_inverseDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  change frobNormRect D * beta + frobNormRect A * invC <=
    d * beta + frobNorm A * invU
  rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hD hbeta)
    (mul_le_mul_of_nonneg_left hInv (frobNorm_nonneg A))

/-- The active componentwise-condition coefficient is dominated by the
source-defined Q-neighborhood coefficient. -/
theorem higham21_sne_conditionDifferenceCoefficient_le_q_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (tau : Real)
    (htau : 0 <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i) :
    higham21SNEConditionDifferenceCoefficient A D
        (undetGramNonsingInv A) tau (higham21SNEQUniformBeta A tau) <=
      higham21SNEQUniformConditionDifferenceCoefficient A tau := by
  let beta := higham21SNEQUniformBeta A tau
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D
    (undetGramNonsingInv A) tau beta
  let pU := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau
  let d := higham21SNEQUniformDirectionFrob A
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hD : frobNorm D <= d := by
    simpa [d] using higham21_sne_direction_frobNorm_le_q_uniform A D hrow
  have hp : pC <= pU := by
    simpa [pC, pU, beta] using
      higham21_sne_pseudoinverseDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  have hp0 : 0 <= pC := by
    exact higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D (undetGramNonsingInv A) tau beta htau hbeta
  have hpU0 : 0 <= pU := hp0.trans hp
  change
    frobNormRect (undetAplusOfGramNonsingInv A) * frobNormRect D +
          pC * frobNormRect A + tau * pC * frobNormRect D <=
      frobNorm (undetAplusOfGramNonsingInv A) * d +
          pU * frobNorm A + tau * pU * d
  rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn,
    frobNormRect_eq_frobNormFn]
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left hD
        (frobNorm_nonneg (undetAplusOfGramNonsingInv A)))
      (mul_le_mul_of_nonneg_right hp (frobNorm_nonneg A)))
    (mul_le_mul
      (mul_le_mul_of_nonneg_left hp htau) hD
      (frobNorm_nonneg D) (mul_nonneg htau hpU0))

/-- The full active condition-times-solution transfer coefficient is
dominated by a coefficient containing no active direction. -/
theorem higham21_sne_conditionTransferCoefficient_le_q_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (tau : Real)
    (htau : 0 <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1)
    (hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i) :
    higham21SNEConditionTransferCoefficient A D b
        (undetGramNonsingInv A) tau (higham21SNEQUniformBeta A tau) <=
      higham21SNEQUniformConditionTransferCoefficient A b tau := by
  let beta := higham21SNEQUniformBeta A tau
  let pC := higham21SNEPseudoinverseDifferenceCoefficient A D
    (undetGramNonsingInv A) tau beta
  let pU := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau
  let cC := higham21SNEConditionDifferenceCoefficient A D
    (undetGramNonsingInv A) tau beta
  let cU := higham21SNEQUniformConditionDifferenceCoefficient A tau
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hp : pC <= pU := by
    simpa [pC, pU, beta] using
      higham21_sne_pseudoinverseDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  have hc : cC <= cU := by
    simpa [cC, cU, beta] using
      higham21_sne_conditionDifferenceCoefficient_le_q_uniform
        A D tau htau hgram hrow
  have hp0 : 0 <= pC := by
    exact higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
      A D (undetGramNonsingInv A) tau beta htau hbeta
  have hc0 : 0 <= cC := by
    exact higham21_sne_conditionDifferenceCoefficient_nonneg
      A D (undetGramNonsingInv A) tau beta htau hbeta
  have hcU0 : 0 <= cU := hc0.trans hc
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let condA := higham21Cond2With A (undetAplusOfGramNonsingInv A)
  have hx0 : 0 <= vecNorm2 x := vecNorm2_nonneg x
  have hb0 : 0 <= vecNorm2 b := vecNorm2_nonneg b
  have hcond0 : 0 <= condA :=
    higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  change cC * vecNorm2 x + condA * (pC * vecNorm2 b) +
      tau * cC * (pC * vecNorm2 b) <=
    cU * vecNorm2 x + condA * (pU * vecNorm2 b) +
      tau * cU * (pU * vecNorm2 b)
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right hc hx0)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp hb0) hcond0))
    (mul_le_mul
      (mul_le_mul_of_nonneg_left hc htau)
      (mul_le_mul_of_nonneg_right hp hb0)
      (mul_nonneg hp0 hb0)
      (mul_nonneg htau hcU0))



































































































































































/-- The exact triangular factor in the nearby Householder QR factorization
has a source-defined Frobenius bound. -/
theorem higham21_sne_householder_R_frobNorm_le_q_uniform
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (tau : Real) (hrho_tau : higham21SNEHouseholderRho fp m k <= tau) :
    frobNorm (higham21SNEHouseholderRHat fp A) <=
      higham21SNEQUniformRBound A tau := by
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let d := higham21SNEQUniformDirectionFrob A
  have hrho : 0 <= rho := hrho_pos.le
  have htau : 0 <= tau := hrho.trans hrho_tau
  have hrow : forall i, rectRowNorm2 D i <= rectRowNorm2 A i := by
    simpa [rho, F, D] using
      higham21_sne_householder_normalized_direction_rowNorm_le
        fp A hm hvalidQR hrho_pos
  have hD : frobNorm D <= d := by
    simpa [d] using higham21_sne_direction_frobNorm_le_q_uniform A D hrow
  have hFeq : F = fun i j => rho * D i j := by
    ext i j
    dsimp [D]
    rw [mul_div_cancel₀ _ (ne_of_gt hrho_pos)]
  have hF : frobNorm F <= tau * d := by
    rw [hFeq, <- frobNormRect_eq_frobNormFn, frobNormRect_smul,
      abs_of_nonneg hrho, frobNormRect_eq_frobNormFn]
    exact (mul_le_mul_of_nonneg_left hD hrho).trans
      (mul_le_mul_of_nonneg_right hrho_tau (by
        dsimp [d, higham21SNEQUniformDirectionFrob,
          higham21Eq21_11UniformDirectionFrobBound]
        exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)))
  have hB : frobNorm B <= frobNorm A + tau * d := by
    calc
      frobNorm B <= frobNorm A + frobNorm F := by
        simpa [B, frobNormRect_eq_frobNormFn] using
          (frobNormRect_add_le A F)
      _ <= frobNorm A + tau * d := add_le_add le_rfl hF
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hQ.rectOpNorm2Le_one
  have hrecover : R = rectMatMul (finiteTranspose Q) (finiteTranspose B) := by
    calc
      R = rectMatMul (idMatrix m) R := (rectMatMul_id_left R).symm
      _ = rectMatMul (rectMatMul (finiteTranspose Q) Q) R := by rw [hQtQ]
      _ = rectMatMul (finiteTranspose Q) (rectMatMul Q R) :=
        rectMatMul_assoc (finiteTranspose Q) Q R
      _ = rectMatMul (finiteTranspose Q) (finiteTranspose B) := by rw [hFactor]
  change frobNorm R <= higham21SNEQUniformRBound A tau
  rw [hrecover]
  calc
    frobNorm (rectMatMul (finiteTranspose Q) (finiteTranspose B)) <=
        frobNorm (finiteTranspose B) := by
      rw [<- frobNormRect_eq_frobNormFn, <- frobNormRect_eq_frobNormFn]
      simpa using
        (frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
          (finiteTranspose Q) (finiteTranspose B) (by norm_num) hQT)
    _ = frobNorm B := by
      rw [<- frobNormRect_eq_frobNormFn, frobNormRect_finiteTranspose,
        frobNormRect_eq_frobNormFn]
    _ <= frobNorm A + tau * d := hB
    _ = higham21SNEQUniformRBound A tau := rfl























































































































































































































































































































































































































/-- Nonnegativity of the source-defined coefficient hierarchy. -/
theorem higham21_sne_q_uniform_coefficient_nonneg
    {m n : Nat} (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (tau : Real) (htau : 0 <= tau)
    (hgram : higham21Eq21_11UniformGramContraction A tau < 1) :
    0 <= higham21SNEQUniformInverseDifferenceCoefficient A tau /\
      0 <= higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau /\
      0 <= higham21SNEQUniformConditionDifferenceCoefficient A tau /\
      0 <= higham21SNEQUniformConditionTransferCoefficient A b tau := by
  let beta := higham21SNEQUniformBeta A tau
  let d := higham21SNEQUniformDirectionFrob A
  let invU := higham21SNEQUniformInverseDifferenceCoefficient A tau
  let pU := higham21SNEQUniformPseudoinverseDifferenceCoefficient A tau
  let cU := higham21SNEQUniformConditionDifferenceCoefficient A tau
  let kcU := higham21SNEQUniformConditionTransferCoefficient A b tau
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21_sne_q_uniform_beta_nonneg A tau hgram
  have hd : 0 <= d := by
    dsimp [d, higham21SNEQUniformDirectionFrob,
      higham21Eq21_11UniformDirectionFrobBound]
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)
  have hGL : 0 <= higham21Eq21_11UniformGramLinearFrobBound A := by
    dsimp [higham21Eq21_11UniformGramLinearFrobBound]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (frobNormRect_nonneg A)) hd
  have hGQ : 0 <= higham21Eq21_11UniformGramQuadraticFrobBound A := by
    dsimp [higham21Eq21_11UniformGramQuadraticFrobBound]
    exact sq_nonneg d
  have hGA : 0 <= higham21Eq21_11UniformGramAbsFrobBound A tau := by
    exact add_nonneg hGL (mul_nonneg htau hGQ)
  have hFirst : 0 <= higham21Eq21_11UniformFirstProductFrobBound A tau := by
    dsimp [higham21Eq21_11UniformFirstProductFrobBound]
    exact mul_nonneg (frobNorm_nonneg (undetGramNonsingInv A)) hGA
  have hIQ : 0 <= higham21Eq21_11UniformInverseQuadraticBound A tau := by
    dsimp [higham21Eq21_11UniformInverseQuadraticBound]
    exact mul_nonneg (sq_nonneg _) hbeta
  have hLL : 0 <= higham21Eq21_11UniformLinearizedLinearBound A := by
    dsimp [higham21Eq21_11UniformLinearizedLinearBound]
    exact mul_nonneg (sq_nonneg _) hGL
  have hLQ : 0 <= higham21Eq21_11UniformLinearizedQuadraticBound A := by
    dsimp [higham21Eq21_11UniformLinearizedQuadraticBound]
    exact mul_nonneg (sq_nonneg _) hGQ
  have hinv : 0 <= invU := by
    dsimp [invU, higham21SNEQUniformInverseDifferenceCoefficient,
      higham21Eq21_11UniformInverseDifferenceBound]
    exact add_nonneg (add_nonneg hLL (mul_nonneg htau hLQ))
      (mul_nonneg htau hIQ)
  have hp : 0 <= pU := by
    dsimp [pU, higham21SNEQUniformPseudoinverseDifferenceCoefficient]
    exact add_nonneg (mul_nonneg hd hbeta)
      (mul_nonneg (frobNorm_nonneg A) hinv)
  have hc : 0 <= cU := by
    dsimp [cU, higham21SNEQUniformConditionDifferenceCoefficient]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (frobNorm_nonneg (undetAplusOfGramNonsingInv A)) hd)
        (mul_nonneg hp (frobNorm_nonneg A)))
      (mul_nonneg (mul_nonneg htau hp) hd)
  have hkc : 0 <= kcU := by
    dsimp [kcU, higham21SNEQUniformConditionTransferCoefficient]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hc (vecNorm2_nonneg _))
        (mul_nonneg
          (higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A))
          (mul_nonneg hp (vecNorm2_nonneg b))))
      (mul_nonneg (mul_nonneg htau hc)
        (mul_nonneg hp (vecNorm2_nonneg b)))
  exact ⟨by simpa [invU] using hinv,
    by simpa [pU] using hp, by simpa [cU] using hc,
    by simpa [kcU] using hkc⟩











































































































































































































































































































































































































/-- Source-defined relative quadratic coefficient for the fully assembled
Householder-SNE forward bound. -/
noncomputable def higham21SNEQUniformRelativeSecondOrderCoefficient
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  higham21SNEQUniformSecondOrderCoefficient A b tau /
    vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b)























































































/-- Dimension-only coefficient converting the SNE master radius to unit
roundoff under the standard half-radius hypotheses. -/
noncomputable def higham21SNEHouseholderThetaUnitRoundoffCoefficient
    (m k : Nat) : Real :=
  2 * ((m : Real) + ((m + k : Nat) : Real) *
    ((m * householderConstructApplyGammaIndex (m + k) : Nat) : Real))

/-- Source-defined coefficient of the explicit `u^2` remainder.  The
absolute value makes the final monotonicity step independent of a separate
nonnegativity API for the relative coefficient. -/
noncomputable def higham21SNEQUniformUnitRoundoffSecondOrderCoefficient
    {m k : Nat} (A : Fin m -> Fin (m + k) -> Real)
    (b : Fin m -> Real) (tau : Real) : Real :=
  higham21SNEHouseholderThetaUnitRoundoffCoefficient m k ^ 2 *
    |higham21SNEQUniformRelativeSecondOrderCoefficient A b tau|
























































































































end NumStability
