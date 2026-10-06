-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A uniform fixed-radius form of the Q-method bound in equation (21.11).

import NumStability.Algorithms.Underdetermined.Higham21Equation21_11

namespace NumStability

set_option maxHeartbeats 1200000

/-- A direction-independent entrywise envelope for every normalized rowwise
    perturbation direction used in equation (21.11). -/
noncomputable def higham21Eq21_11UniformDirectionEnvelope {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun _ _ => frobNormRect A

/-- The induced Gram-perturbation envelope at the fixed radius `rho`. -/
noncomputable def higham21Eq21_11UniformGramEnvelope {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Fin m -> Fin m -> Real :=
  undetGramPerturbationComponentBudget A
    (higham21Eq21_11UniformDirectionEnvelope A) rho

/-- The fixed-radius Chapter 7 contraction controlling all perturbed Gram
    inverses arising from normalized rowwise directions. -/
noncomputable def higham21Eq21_11UniformGramContraction {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  rho * infNorm
    (ch7InverseFirstProductSensitivity m (undetGramNonsingInv A)
      (higham21Eq21_11UniformGramEnvelope A rho))

/-- One contraction condition at `rho` packages both the Q-method smallness
    condition and the uniform perturbed-Gram inverse condition. -/
noncomputable def higham21Eq21_11UniformContraction {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  max
    (rho * higham21Cond2With A (undetAplusOfGramNonsingInv A))
    (higham21Eq21_11UniformGramContraction A rho)

/-- A direction- and parameter-independent Frobenius bound for every
    perturbed Gram inverse in the fixed `rho` neighborhood. -/
noncomputable def higham21Eq21_11UniformGramInverseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  let c := higham21Eq21_11UniformGramContraction A rho
  Real.sqrt ((m : Real) * (m : Real)) *
    (((m : Real) * (1 / (1 - c))) * infNorm (undetGramNonsingInv A))

/-- A direction-independent Frobenius bound obtained from the uniform entry
    envelope. -/
noncomputable def higham21Eq21_11UniformDirectionFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  Real.sqrt ((m : Real) * (n : Real)) * frobNormRect A

noncomputable def higham21Eq21_11UniformGramLinearFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  2 * frobNormRect A * higham21Eq21_11UniformDirectionFrobBound A

noncomputable def higham21Eq21_11UniformGramQuadraticFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  higham21Eq21_11UniformDirectionFrobBound A ^ 2

noncomputable def higham21Eq21_11UniformGramAbsFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformGramLinearFrobBound A +
    rho * higham21Eq21_11UniformGramQuadraticFrobBound A

noncomputable def higham21Eq21_11UniformFirstProductFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  frobNorm (undetGramNonsingInv A) *
    higham21Eq21_11UniformGramAbsFrobBound A rho

noncomputable def higham21Eq21_11UniformInverseQuadraticBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformFirstProductFrobBound A rho ^ 2 *
    higham21Eq21_11UniformGramInverseBound A rho

noncomputable def higham21Eq21_11UniformLinearizedLinearBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  frobNorm (undetGramNonsingInv A) ^ 2 *
    higham21Eq21_11UniformGramLinearFrobBound A

noncomputable def higham21Eq21_11UniformLinearizedQuadraticBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  frobNorm (undetGramNonsingInv A) ^ 2 *
    higham21Eq21_11UniformGramQuadraticFrobBound A

noncomputable def higham21Eq21_11UniformInverseDifferenceBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformLinearizedLinearBound A +
    rho * higham21Eq21_11UniformLinearizedQuadraticBound A +
    rho * higham21Eq21_11UniformInverseQuadraticBound A rho

noncomputable def higham21Eq21_11UniformCancellationBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformLinearizedQuadraticBound A +
    higham21Eq21_11UniformInverseQuadraticBound A rho

/-- The absolute quadratic remainder coefficient.  It contains no normalized
    direction and no actual perturbation parameter. -/
noncomputable def higham21Eq21_11UniformAbsoluteCoefficient {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (rho : Real) : Real :=
  frobNormRect A * higham21Eq21_11UniformCancellationBound A rho * vecNorm2 b +
    higham21Eq21_11UniformDirectionFrobBound A *
      higham21Eq21_11UniformInverseDifferenceBound A rho * vecNorm2 b

/-- The relative fixed-radius coefficient in the uniform form of (21.11).
    It depends only on `A`, `b`, `rho`, and the matrix dimensions. -/
noncomputable def higham21Eq21_11UniformRelativeCoefficient {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformAbsoluteCoefficient A b rho /
    vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b)

private theorem higham21Eq21_11_rectRowNorm2_le_frobNormRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (i : Fin m) :
    rectRowNorm2 A i <= frobNormRect A := by
  unfold rectRowNorm2 vecNorm2 frobNormRect
  apply Real.sqrt_le_sqrt
  simpa [frobNormSqRect, frobNormSq] using
    (vecNorm2Sq_row_le_frobNormSq A i)

private theorem higham21Eq21_11UniformDirectionEnvelope_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    forall i j, 0 <= higham21Eq21_11UniformDirectionEnvelope A i j := by
  intro i j
  exact frobNormRect_nonneg A

private theorem higham21Eq21_11_direction_entry_le_uniform_envelope
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    forall i j, |D i j| <= higham21Eq21_11UniformDirectionEnvelope A i j := by
  intro i j
  calc
    |D i j| <= rectRowNorm2 D i := by
      simpa [rectRowNorm2] using
        (abs_coord_le_vecNorm2 (fun q : Fin n => D i q) j)
    _ <= rectRowNorm2 A i := hrow i
    _ <= frobNormRect A := higham21Eq21_11_rectRowNorm2_le_frobNormRect A i
    _ = higham21Eq21_11UniformDirectionEnvelope A i j := rfl

private theorem higham21Eq21_11UniformDirectionFrobBound_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21Eq21_11UniformDirectionFrobBound A := by
  exact mul_nonneg (Real.sqrt_nonneg _) (frobNormRect_nonneg A)

private theorem higham21Eq21_11_direction_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNormRect D <= higham21Eq21_11UniformDirectionFrobBound A := by
  simpa [higham21Eq21_11UniformDirectionFrobBound] using
    (frobNormRect_le_sqrt_mul_nat_of_entry_abs_le D
      (frobNormRect_nonneg A)
      (higham21Eq21_11_direction_entry_le_uniform_envelope A D hrow))

private theorem higham21Eq21_11_gramLinear_eq_products {m n : Nat}
    (A D : Fin m -> Fin n -> Real) :
    higham21Eq21_7GramLinear A D = fun i r =>
      rectMatMul A (finiteTranspose D) i r +
        rectMatMul D (finiteTranspose A) i r := by
  ext i r
  simp only [higham21Eq21_7GramLinear, rectMatMul, finiteTranspose]
  rw [Finset.sum_add_distrib]

private theorem higham21Eq21_11_gramQuadratic_eq_product {m n : Nat}
    (D : Fin m -> Fin n -> Real) :
    higham21Eq21_7GramQuadratic D = rectMatMul D (finiteTranspose D) := by
  ext i j
  rfl

private theorem higham21Eq21_11_frobNorm_absMatrix {n : Nat}
    (M : Fin n -> Fin n -> Real) :
    frobNorm (absMatrix n M) = frobNorm M := by
  rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
  simpa [absMatrix] using (frobNormRect_abs M)

private theorem higham21Eq21_11_frobNorm_smul_nonneg {n : Nat}
    (a : Real) (ha : 0 <= a) (M : Fin n -> Fin n -> Real) :
    frobNorm (fun i j => a * M i j) = a * frobNorm M := by
  rw [← frobNormRect_eq_frobNormFn, frobNormRect_smul,
    abs_of_nonneg ha, frobNormRect_eq_frobNormFn]

private theorem higham21Eq21_11_gramLinear_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNorm (higham21Eq21_7GramLinear A D) <=
      higham21Eq21_11UniformGramLinearFrobBound A := by
  let a := frobNormRect A
  let dnorm := frobNormRect D
  let d := higham21Eq21_11UniformDirectionFrobBound A
  have hD : dnorm <= d :=
    higham21Eq21_11_direction_frobNorm_le_uniform A D hrow
  calc
    frobNorm (higham21Eq21_7GramLinear A D) =
        frobNormRect (fun i r =>
          rectMatMul A (finiteTranspose D) i r +
            rectMatMul D (finiteTranspose A) i r) := by
      rw [higham21Eq21_11_gramLinear_eq_products,
        frobNormRect_eq_frobNormFn]
    _ <= frobNormRect (rectMatMul A (finiteTranspose D)) +
          frobNormRect (rectMatMul D (finiteTranspose A)) :=
      frobNormRect_add_le _ _
    _ <= a * dnorm + dnorm * a := by
      exact add_le_add
        (by simpa [a, dnorm, frobNormRect_finiteTranspose] using
          (frobNormRect_rectMatMul_le A (finiteTranspose D)))
        (by simpa [a, dnorm, frobNormRect_finiteTranspose] using
          (frobNormRect_rectMatMul_le D (finiteTranspose A)))
    _ = 2 * a * dnorm := by ring
    _ <= 2 * a * d :=
      mul_le_mul_of_nonneg_left hD
        (mul_nonneg (by norm_num) (frobNormRect_nonneg A))
    _ = higham21Eq21_11UniformGramLinearFrobBound A := by
      rfl

private theorem higham21Eq21_11_gramQuadratic_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNorm (higham21Eq21_7GramQuadratic D) <=
      higham21Eq21_11UniformGramQuadraticFrobBound A := by
  let dnorm := frobNormRect D
  let d := higham21Eq21_11UniformDirectionFrobBound A
  have hD : dnorm <= d :=
    higham21Eq21_11_direction_frobNorm_le_uniform A D hrow
  have hd : 0 <= d := higham21Eq21_11UniformDirectionFrobBound_nonneg A
  calc
    frobNorm (higham21Eq21_7GramQuadratic D) =
        frobNormRect (rectMatMul D (finiteTranspose D)) := by
      rw [higham21Eq21_11_gramQuadratic_eq_product,
        frobNormRect_eq_frobNormFn]
    _ <= dnorm * dnorm := by
      simpa [dnorm, frobNormRect_finiteTranspose] using
        (frobNormRect_rectMatMul_le D (finiteTranspose D))
    _ <= d * d :=
      mul_le_mul hD hD (frobNormRect_nonneg D) hd
    _ = higham21Eq21_11UniformGramQuadraticFrobBound A := by
      simp [higham21Eq21_11UniformGramQuadraticFrobBound, d, pow_two]

private theorem higham21Eq21_11_linearized_eq_product {m : Nat}
    (G M : Fin m -> Fin m -> Real) :
    higham21Eq21_7LinearizedMatrix G M = matMul m (matMul m G M) G := by
  ext i j
  exact ch7InverseLinearizedEntry_eq_matMul m G M i j

private theorem higham21Eq21_11_linearized_frobNorm_le
    {m : Nat} (G M : Fin m -> Fin m -> Real) (s : Real)
    (hM : frobNorm M <= s) :
    frobNorm (higham21Eq21_7LinearizedMatrix G M) <=
      frobNorm G ^ 2 * s := by
  have hG : 0 <= frobNorm G := frobNorm_nonneg G
  calc
    frobNorm (higham21Eq21_7LinearizedMatrix G M) =
        frobNorm (matMul m (matMul m G M) G) := by
      rw [higham21Eq21_11_linearized_eq_product]
    _ <= frobNorm (matMul m G M) * frobNorm G :=
      frobNorm_matMul_le (matMul m G M) G
    _ <= (frobNorm G * frobNorm M) * frobNorm G :=
      mul_le_mul_of_nonneg_right (frobNorm_matMul_le G M) hG
    _ <= (frobNorm G * s) * frobNorm G :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM hG) hG
    _ = frobNorm G ^ 2 * s := by ring

private theorem higham21Eq21_11_gramAbs_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNorm (higham21Eq21_7GramAbsEnvelope A D rho) <=
      higham21Eq21_11UniformGramAbsFrobBound A rho := by
  let H := higham21Eq21_7GramLinear A D
  let K := higham21Eq21_7GramQuadratic D
  have hH : frobNorm H <= higham21Eq21_11UniformGramLinearFrobBound A := by
    simpa [H] using higham21Eq21_11_gramLinear_frobNorm_le_uniform A D hrow
  have hK : frobNorm K <= higham21Eq21_11UniformGramQuadraticFrobBound A := by
    simpa [K] using higham21Eq21_11_gramQuadratic_frobNorm_le_uniform A D hrow
  change frobNorm (fun i j => |H i j| + rho * |K i j|) <= _
  calc
    frobNorm (fun i j => |H i j| + rho * |K i j|) <=
        frobNorm (absMatrix m H) +
          frobNorm (fun i j => rho * absMatrix m K i j) := by
      simpa [absMatrix] using
        (frobNorm_add_le (absMatrix m H)
          (fun i j => rho * absMatrix m K i j))
    _ = frobNorm H + rho * frobNorm K := by
      rw [higham21Eq21_11_frobNorm_absMatrix,
        higham21Eq21_11_frobNorm_smul_nonneg rho hrho,
        higham21Eq21_11_frobNorm_absMatrix]
    _ <= higham21Eq21_11UniformGramLinearFrobBound A +
          rho * higham21Eq21_11UniformGramQuadraticFrobBound A :=
      add_le_add hH (mul_le_mul_of_nonneg_left hK hrho)
    _ = higham21Eq21_11UniformGramAbsFrobBound A rho := rfl

private theorem higham21Eq21_11_firstProduct_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    frobNorm
        (ch7InverseFirstProductSensitivity m (undetGramNonsingInv A)
          (higham21Eq21_7GramAbsEnvelope A D rho)) <=
      higham21Eq21_11UniformFirstProductFrobBound A rho := by
  let G := undetGramNonsingInv A
  let Ebar := higham21Eq21_7GramAbsEnvelope A D rho
  have hE : frobNorm Ebar <= higham21Eq21_11UniformGramAbsFrobBound A rho := by
    simpa [Ebar] using
      higham21Eq21_11_gramAbs_frobNorm_le_uniform A D rho hrho hrow
  calc
    frobNorm (ch7InverseFirstProductSensitivity m G Ebar) <=
        frobNorm (absMatrix m G) * frobNorm Ebar := by
      exact frobNorm_matMul_le (absMatrix m G) Ebar
    _ = frobNorm G * frobNorm Ebar := by
      rw [higham21Eq21_11_frobNorm_absMatrix]
    _ <= frobNorm G * higham21Eq21_11UniformGramAbsFrobBound A rho :=
      mul_le_mul_of_nonneg_left hE (frobNorm_nonneg G)
    _ = higham21Eq21_11UniformFirstProductFrobBound A rho := rfl

private theorem higham21Eq21_11UniformGramContraction_nonneg
    {m n : Nat} (A : Fin m -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho) :
    0 <= higham21Eq21_11UniformGramContraction A rho := by
  exact mul_nonneg hrho (infNorm_nonneg _)

private theorem higham21Eq21_11UniformGramInverseBound_nonneg
    {m n : Nat} (A : Fin m -> Fin n -> Real) (rho : Real)
    (hgram : higham21Eq21_11UniformGramContraction A rho < 1) :
    0 <= higham21Eq21_11UniformGramInverseBound A rho := by
  let c := higham21Eq21_11UniformGramContraction A rho
  have hden : 0 < 1 - c := sub_pos.mpr (by simpa [c] using hgram)
  change 0 <= Real.sqrt ((m : Real) * (m : Real)) *
    (((m : Real) * (1 / (1 - c))) * infNorm (undetGramNonsingInv A))
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le m) (one_div_pos.mpr hden).le)
      (infNorm_nonneg _))

private theorem higham21Eq21_11_fixedRadiusCoefficient_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hgram : higham21Eq21_11UniformGramContraction A rho < 1)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) :
    higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
        (undetGramNonsingInv A) rho
        (higham21Eq21_11UniformGramInverseBound A rho) <=
      higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
  let G := undetGramNonsingInv A
  let H := higham21Eq21_7GramLinear A D
  let K := higham21Eq21_7GramQuadratic D
  let LH := higham21Eq21_7LinearizedMatrix G H
  let LK := higham21Eq21_7LinearizedMatrix G K
  let Ebar := higham21Eq21_7GramAbsEnvelope A D rho
  let P := ch7InverseFirstProductSensitivity m G Ebar
  let beta := higham21Eq21_11UniformGramInverseBound A rho
  let a := frobNormRect A
  let dnorm := frobNormRect D
  let d := higham21Eq21_11UniformDirectionFrobBound A
  let bnorm := vecNorm2 b
  have hbeta : 0 <= beta := by
    simpa [beta] using
      higham21Eq21_11UniformGramInverseBound_nonneg A rho hgram
  have hD : dnorm <= d := by
    simpa [dnorm, d] using
      higham21Eq21_11_direction_frobNorm_le_uniform A D hrow
  have hd : 0 <= d := by
    simpa [d] using higham21Eq21_11UniformDirectionFrobBound_nonneg A
  have hH : frobNorm H <= higham21Eq21_11UniformGramLinearFrobBound A := by
    simpa [H] using
      higham21Eq21_11_gramLinear_frobNorm_le_uniform A D hrow
  have hK : frobNorm K <= higham21Eq21_11UniformGramQuadraticFrobBound A := by
    simpa [K] using
      higham21Eq21_11_gramQuadratic_frobNorm_le_uniform A D hrow
  have hLH :
      frobNorm LH <= higham21Eq21_11UniformLinearizedLinearBound A := by
    simpa [LH, G, higham21Eq21_11UniformLinearizedLinearBound] using
      higham21Eq21_11_linearized_frobNorm_le G H
        (higham21Eq21_11UniformGramLinearFrobBound A) hH
  have hLK :
      frobNorm LK <= higham21Eq21_11UniformLinearizedQuadraticBound A := by
    simpa [LK, G, higham21Eq21_11UniformLinearizedQuadraticBound] using
      higham21Eq21_11_linearized_frobNorm_le G K
        (higham21Eq21_11UniformGramQuadraticFrobBound A) hK
  have hP : frobNorm P <= higham21Eq21_11UniformFirstProductFrobBound A rho := by
    simpa [P, G, Ebar] using
      higham21Eq21_11_firstProduct_frobNorm_le_uniform A D rho hrho hrow
  have hGramLinear0 : 0 <= higham21Eq21_11UniformGramLinearFrobBound A := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (frobNormRect_nonneg A)) hd
  have hGramQuadratic0 :
      0 <= higham21Eq21_11UniformGramQuadraticFrobBound A := by
    exact sq_nonneg _
  have hGramAbs0 : 0 <= higham21Eq21_11UniformGramAbsFrobBound A rho := by
    exact add_nonneg hGramLinear0 (mul_nonneg hrho hGramQuadratic0)
  have hFirstProduct0 :
      0 <= higham21Eq21_11UniformFirstProductFrobBound A rho := by
    exact mul_nonneg (frobNorm_nonneg G) hGramAbs0
  have hP2 : frobNorm P ^ 2 <=
      higham21Eq21_11UniformFirstProductFrobBound A rho ^ 2 :=
    (sq_le_sq₀ (frobNorm_nonneg P) hFirstProduct0).mpr hP
  have hIQ : frobNorm P ^ 2 * beta <=
      higham21Eq21_11UniformInverseQuadraticBound A rho := by
    simpa [beta, higham21Eq21_11UniformInverseQuadraticBound] using
      mul_le_mul_of_nonneg_right hP2 hbeta
  have hDifference :
      frobNorm LH + rho * frobNorm LK + rho * (frobNorm P ^ 2 * beta) <=
        higham21Eq21_11UniformInverseDifferenceBound A rho := by
    calc
      frobNorm LH + rho * frobNorm LK + rho * (frobNorm P ^ 2 * beta) <=
          higham21Eq21_11UniformLinearizedLinearBound A +
            rho * higham21Eq21_11UniformLinearizedQuadraticBound A +
            rho * higham21Eq21_11UniformInverseQuadraticBound A rho :=
        add_le_add
          (add_le_add hLH (mul_le_mul_of_nonneg_left hLK hrho))
          (mul_le_mul_of_nonneg_left hIQ hrho)
      _ = higham21Eq21_11UniformInverseDifferenceBound A rho := rfl
  have hCancellation :
      frobNorm LK + frobNorm P ^ 2 * beta <=
        higham21Eq21_11UniformCancellationBound A rho := by
    calc
      frobNorm LK + frobNorm P ^ 2 * beta <=
          higham21Eq21_11UniformLinearizedQuadraticBound A +
            higham21Eq21_11UniformInverseQuadraticBound A rho :=
        add_le_add hLK hIQ
      _ = higham21Eq21_11UniformCancellationBound A rho := rfl
  have hDifference0 :
      0 <= frobNorm LH + rho * frobNorm LK +
        rho * (frobNorm P ^ 2 * beta) := by
    exact add_nonneg
      (add_nonneg (frobNorm_nonneg LH)
        (mul_nonneg hrho (frobNorm_nonneg LK)))
      (mul_nonneg hrho (mul_nonneg (sq_nonneg _) hbeta))
  have hCoefficient :
      higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
          G rho beta =
        a * (frobNorm LK + frobNorm P ^ 2 * beta) * bnorm +
          dnorm *
            (frobNorm LH + rho * frobNorm LK +
              rho * (frobNorm P ^ 2 * beta)) * bnorm := by
    have hzeroNorm : vecNorm2 (0 : Fin m -> Real) = 0 := by
      simpa only [Pi.zero_apply] using (vecNorm2_zero (n := m))
    simp [higham21Eq21_7FixedRadiusCoefficient,
      higham21Eq21_7InverseDifferenceCoefficient,
      higham21Eq21_7CancellationCoefficient,
      higham21Eq21_7InverseQuadraticCoefficient,
      G, H, K, LH, LK, Ebar, P, beta, a, dnorm, bnorm, hzeroNorm]
  change higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
    G rho beta <= higham21Eq21_11UniformAbsoluteCoefficient A b rho
  rw [hCoefficient]
  calc
    a * (frobNorm LK + frobNorm P ^ 2 * beta) * bnorm +
          dnorm *
            (frobNorm LH + rho * frobNorm LK +
              rho * (frobNorm P ^ 2 * beta)) * bnorm <=
        a * higham21Eq21_11UniformCancellationBound A rho * bnorm +
          d * higham21Eq21_11UniformInverseDifferenceBound A rho * bnorm := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCancellation (frobNormRect_nonneg A))
          (vecNorm2_nonneg b)
      · have hproduct :
            dnorm *
                (frobNorm LH + rho * frobNorm LK +
                  rho * (frobNorm P ^ 2 * beta)) <=
              d * higham21Eq21_11UniformInverseDifferenceBound A rho :=
          mul_le_mul hD hDifference hDifference0 hd
        exact mul_le_mul_of_nonneg_right hproduct (vecNorm2_nonneg b)
    _ = higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
      rfl

/-- The fixed contraction at `rho` bounds the inverse of every scaled Gram
    matrix generated by a normalized rowwise direction and every
    `0 <= eta <= rho`. -/
theorem higham21Eq21_11_scaled_gramInverse_frobNorm_le_uniform
    {m n : Nat} (A D : Fin m -> Fin n -> Real)
    (rho eta : Real) (hm : 0 < m)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho : 0 <= rho) (heta : 0 <= eta) (heta_rho : eta <= rho)
    (hrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i)
    (hgram : higham21Eq21_11UniformGramContraction A rho < 1) :
    frobNorm
        (undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D eta)) <=
      higham21Eq21_11UniformGramInverseBound A rho := by
  let E : Fin m -> Fin n -> Real :=
    higham21Eq21_11UniformDirectionEnvelope A
  let F : Fin m -> Fin m -> Real :=
    higham21Eq21_11UniformGramEnvelope A rho
  let G : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let Delta : Fin m -> Fin n -> Real := fun i j => eta * D i j
  let c : Real := higham21Eq21_11UniformGramContraction A rho
  have hE : forall i j, 0 <= E i j := by
    simpa [E] using higham21Eq21_11UniformDirectionEnvelope_nonneg A
  have hDelta : forall i j, |Delta i j| <= rho * E i j := by
    intro i j
    have hentry :=
      higham21Eq21_11_direction_entry_le_uniform_envelope A D hrow i j
    calc
      |Delta i j| = eta * |D i j| := by
        simp [Delta, abs_mul, abs_of_nonneg heta]
      _ <= eta * E i j := mul_le_mul_of_nonneg_left hentry heta
      _ <= rho * E i j :=
        mul_le_mul_of_nonneg_right heta_rho (hE i j)
  have hF : forall i j, 0 <= F i j := by
    simpa [F, E, higham21Eq21_11UniformGramEnvelope] using
      undetGramPerturbationComponentBudget_nonneg A E hrho hE
  have hDeltaG : forall i j,
      |undetGramPerturbation A Delta i j| <= rho * F i j := by
    simpa [F, higham21Eq21_11UniformGramEnvelope, E] using
      undetGramPerturbation_abs_le_componentBudget
        A Delta E hrho hE hDelta
  have hc : 0 <= c := by
    simpa [c] using higham21Eq21_11UniformGramContraction_nonneg A rho hrho
  have hc_lt : c < 1 := by simpa [c] using hgram
  have hLeft : IsLeftInverse m (rectGram A) G := by
    simpa [G, undetGramNonsingInv] using
      (isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet).1
  have hbound :
      infNormBound m
        (absMatrix m (matMul m G (undetGramPerturbation A Delta))) c := by
    simpa [c, F, E, G, higham21Eq21_11UniformGramContraction,
      higham21Eq21_11UniformGramEnvelope] using
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A Delta G F rho hrho hF hDeltaG
  have hInvEq :
      undetGramNonsingInv (fun i j => A i j + Delta i j) =
        ch7Problem711PerturbedInverseCandidate m G
          (undetGramPerturbation A Delta) :=
    higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
      hm A Delta G c hc hc_lt hLeft hbound
  have hCandidate :
      frobNorm
          (ch7Problem711PerturbedInverseCandidate m G
            (undetGramPerturbation A Delta)) <=
        Real.sqrt ((m : Real) * (m : Real)) *
          (((m : Real) * (1 / (1 - c))) * infNorm G) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm G (undetGramPerturbation A Delta) c hc hc_lt hbound
  have hscaled :
      higham21Eq21_7ScaledMatrix A D eta =
        fun i j => A i j + Delta i j := by
    rfl
  rw [hscaled, hInvEq]
  simpa [higham21Eq21_11UniformGramInverseBound, c, G] using hCandidate

/-- Higham, 2nd ed., Chapter 21, equation (21.11), with one uniform
    fixed-radius quadratic coefficient.

    The coefficient contains neither the actual `eta` nor the existential
    normalized direction supplied by backward stability.  The hypothesis
    `2 <= m + k` replaces the older strict-underdetermination assumption, so
    the existing Q-method API also covers the square branch `k = 0` whenever
    `2 <= m`. -/
theorem higham21_eq21_11_computed_qhat_relative_forward_error_uniform
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (rho : Real) (hm : 0 < m) (hN : 2 <= m + k) (hb : b ≠ 0)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hEtaRadius :
      0 <= gamma fp (Higham21QMethodRoundedGammaIndex m k) /\
      gamma fp (Higham21QMethodRoundedGammaIndex m k) <= rho)
    (hcontract : higham21Eq21_11UniformContraction A rho < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      ((m + k : Nat) : Real) * eta *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        eta ^ 2 * higham21Eq21_11UniformRelativeCoefficient A b rho := by
  dsimp only
  let x_hat : Fin (m + k) -> Real :=
    higham21Eq21_11ComputedQhat fp m k A b
  let Aplus : Fin (m + k) -> Fin m -> Real :=
    undetAplusOfGramNonsingInv A
  let x : Fin (m + k) -> Real := rectMatMulVec Aplus b
  let eta : Real := gamma fp (Higham21QMethodRoundedGammaIndex m k)
  let cond : Real := higham21Cond2With A Aplus
  let gramC : Real := higham21Eq21_11UniformGramContraction A rho
  change vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
    ((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus +
      eta ^ 2 * higham21Eq21_11UniformRelativeCoefficient A b rho
  have hrho : 0 <= rho := le_trans hEtaRadius.1 hEtaRadius.2
  have hcontract' : max (rho * cond) gramC < 1 := by
    simpa [higham21Eq21_11UniformContraction, cond, Aplus, gramC] using hcontract
  have hmethod : rho * cond < 1 :=
    (le_max_left (rho * cond) gramC).trans_lt hcontract'
  have hgram : gramC < 1 :=
    (le_max_right (rho * cond) gramC).trans_lt hcontract'
  have hcond_nonneg : 0 <= cond := by
    simpa [cond, Aplus] using
      higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  have hCondSmall : eta * cond < 1 := by
    exact
      (mul_le_mul_of_nonneg_right hEtaRadius.2 hcond_nonneg).trans_lt hmethod
  have hdetA :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_qmethod_full_row_rank_gram_det_ne_zero hdomain
  obtain ⟨DeltaA, hfeas, hdetDelta⟩ :=
    higham21_theorem21_4_computed_qhat_rank_stable_gamma
      fp A b hm hdomain hvalid
        (by simpa [eta, cond, Aplus] using hCondSmall)
  by_cases heta_zero : eta = 0
  · have hrow_zero : forall i : Fin m, rectRowNorm2 DeltaA i = 0 := by
      intro i
      apply le_antisymm
      · have heta_zero' :
            gamma fp (Higham21QMethodRoundedGammaIndex m k) = 0 := by
          simpa [eta] using heta_zero
        simpa [heta_zero'] using hfeas.row_bound i
      · exact rectRowNorm2_nonneg DeltaA i
    have hDeltaA : DeltaA = 0 := by
      funext i j
      exact
        (vecNorm2_eq_zero_iff (fun q : Fin (m + k) => DeltaA i q)).mp
          (by simpa [rectRowNorm2] using hrow_zero i) j
    have hxhatMin : RectMinNormSolution m (m + k) A b x_hat := by
      simpa [hDeltaA] using hfeas.min_norm
    have hxMin : RectMinNormSolution m (m + k) A b x := by
      simpa [x, Aplus] using
        higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
          A b hdetA
    obtain ⟨z, hz⟩ := hxMin.exists_transpose_witness
    have hzsolve : rectMatMulVec A (rectTransposeMulVec A z) = b := by
      rw [hz]
      exact hxMin.system_eq
    have hxhat_eq : x_hat = x :=
      (rectMinNormSolution_eq_of_transpose_solution
        A b x_hat z hxhatMin hzsolve).trans hz
    simp [hxhat_eq, heta_zero, vecNorm2_zero]
  · have heta_pos : 0 < eta :=
      lt_of_le_of_ne hEtaRadius.1 (Ne.symm heta_zero)
    let D : Fin m -> Fin (m + k) -> Real := fun i j => DeltaA i j / eta
    have hDeltaScale : forall i j, DeltaA i j = eta * D i j := by
      intro i j
      dsimp [D]
      field_simp [heta_pos.ne']
    have hDrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i := by
      intro i
      have hnorm :
          rectRowNorm2 D i = eta⁻¹ * rectRowNorm2 DeltaA i := by
        calc
          rectRowNorm2 D i =
              vecNorm2
                (fun j : Fin (m + k) => eta⁻¹ * DeltaA i j) := by
            unfold rectRowNorm2
            congr 1
            funext j
            simp [D, div_eq_mul_inv, mul_comm]
          _ = |eta⁻¹| * rectRowNorm2 DeltaA i :=
            vecNorm2_smul eta⁻¹ (fun j : Fin (m + k) => DeltaA i j)
          _ = eta⁻¹ * rectRowNorm2 DeltaA i := by
            rw [abs_of_pos (inv_pos.mpr heta_pos)]
      rw [hnorm]
      calc
        eta⁻¹ * rectRowNorm2 DeltaA i <=
            eta⁻¹ * (eta * rectRowNorm2 A i) :=
          mul_le_mul_of_nonneg_left (hfeas.row_bound i)
            (inv_nonneg.mpr hEtaRadius.1)
        _ = rectRowNorm2 A i := by field_simp [heta_pos.ne']
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + DeltaA i j
    have hscaledMatrix : higham21Eq21_7ScaledMatrix A D eta = B := by
      ext i j
      simp only [higham21Eq21_7ScaledMatrix, B]
      rw [hDeltaScale i j]
    have hdetScaled :
        Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A D eta) :
            Matrix (Fin m) (Fin m) Real) ≠ 0 := by
      simpa [hscaledMatrix, B] using hdetDelta
    let Gt : Fin m -> Fin m -> Real :=
      undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D eta)
    have hxhatFormula :=
      higham21_lemma21_2_transpose_range_of_min_norm_and_perturbed_gram_det_ne_zero
        A DeltaA b x_hat hfeas.min_norm hdetDelta
    have hscaledRhs :
        higham21Eq21_7ScaledRhs b (0 : Fin m -> Real) eta = b := by
      funext i
      simp [higham21Eq21_7ScaledRhs]
    have hperturbed :
        higham21Eq21_7PerturbedSolution A D b (0 : Fin m -> Real) Gt eta =
          x_hat := by
      calc
        higham21Eq21_7PerturbedSolution A D b (0 : Fin m -> Real) Gt eta =
            rectMatMulVec
              (undetAplusOfGramInv B (undetGramNonsingInv B)) b := by
          simp [higham21Eq21_7PerturbedSolution,
            Gt, hscaledMatrix, hscaledRhs, B]
        _ = rectTransposeMulVec B (matMulVec m (undetGramNonsingInv B) b) :=
          rectMatMulVec_undetAplusOfGramInv B (undetGramNonsingInv B) b
        _ = x_hat := by simpa [B] using hxhatFormula.symm
    have hbase :
        higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) = x := by
      rfl
    have hfirst :
        higham21Eq21_11FirstOrder A D b =
          higham21Eq21_7FirstOrder A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A) :=
      higham21_eq21_11_firstOrder_eq_eq21_7_firstOrder A D b hdetA
    have hexact :
        (fun j => x_hat j - x j) = fun j =>
          eta * higham21Eq21_11FirstOrder A D b j +
            higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
              (undetGramNonsingInv A) Gt eta j := by
      have h := higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
        A D b (0 : Fin m -> Real) eta hdetA hdetScaled
      rw [hperturbed, hbase, ← hfirst] at h
      simpa [Gt] using h
    let beta : Real := higham21Eq21_11UniformGramInverseBound A rho
    have hbeta : 0 <= beta := by
      simpa [beta, gramC] using
        higham21Eq21_11UniformGramInverseBound_nonneg A rho hgram
    have hGt : frobNorm Gt <= beta := by
      simpa [Gt, beta, gramC] using
        higham21Eq21_11_scaled_gramInverse_frobNorm_le_uniform
          A D rho eta hm hdetA hrho hEtaRadius.1 hEtaRadius.2 hDrow hgram
    have hfixed :=
      higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
        A D b (0 : Fin m -> Real) (undetGramNonsingInv A) Gt
        rho beta eta hrho hbeta
        (by simpa [abs_of_pos heta_pos] using hEtaRadius.2) hGt
    have hcoefficient :
        higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A) rho beta <=
          higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
      simpa [beta, gramC] using
        higham21Eq21_11_fixedRadiusCoefficient_le_uniform
          A D b rho hrho hgram hDrow
    have hremainder :
        vecNorm2
            (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
              (undetGramNonsingInv A) Gt eta) <=
          eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
      calc
        vecNorm2
            (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
              (undetGramNonsingInv A) Gt eta) <=
            |eta| ^ 2 *
              higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
                (undetGramNonsingInv A) rho beta := hfixed
        _ <= |eta| ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho :=
          mul_le_mul_of_nonneg_left hcoefficient (sq_nonneg |eta|)
        _ = eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
          rw [abs_of_pos heta_pos]
    have hfirstBound :
        vecNorm2 (higham21Eq21_11FirstOrder A D b) <=
          ((m + k : Nat) : Real) *
            higham21Cond2With A Aplus * vecNorm2 x := by
      simpa [Aplus, x] using
        higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
          A D b hN hdetA (by norm_num : (0 : Real) <= 1)
          (by simpa using hDrow)
    have habsolute :
        vecNorm2 (fun j => x_hat j - x j) <=
          ((m + k : Nat) : Real) * eta *
              higham21Cond2With A Aplus * vecNorm2 x +
            eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
      calc
        vecNorm2 (fun j => x_hat j - x j) =
            vecNorm2 (fun j =>
              eta * higham21Eq21_11FirstOrder A D b j +
                higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
                  (undetGramNonsingInv A) Gt eta j) :=
          congrArg vecNorm2 hexact
        _ <= vecNorm2 (fun j => eta * higham21Eq21_11FirstOrder A D b j) +
            vecNorm2
              (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
                (undetGramNonsingInv A) Gt eta) := vecNorm2_add_le _ _
        _ = eta * vecNorm2 (higham21Eq21_11FirstOrder A D b) +
            vecNorm2
              (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
                (undetGramNonsingInv A) Gt eta) := by
          rw [vecNorm2_smul, abs_of_pos heta_pos]
        _ <= eta *
              (((m + k : Nat) : Real) *
                higham21Cond2With A Aplus * vecNorm2 x) +
            eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho :=
          add_le_add
            (mul_le_mul_of_nonneg_left hfirstBound hEtaRadius.1) hremainder
        _ = ((m + k : Nat) : Real) * eta *
              higham21Cond2With A Aplus * vecNorm2 x +
            eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho := by
          ring
    have hxMin : RectMinNormSolution m (m + k) A b x := by
      simpa [x, Aplus] using
        higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
          A b hdetA
    have hxne : x ≠ 0 := by
      intro hx0
      apply hb
      rw [← hxMin.system_eq, hx0]
      ext i
      simp [rectMatMulVec]
    have hxnorm_ne : vecNorm2 x ≠ 0 := by
      intro hxnorm
      apply hxne
      ext j
      exact (vecNorm2_eq_zero_iff x).mp hxnorm j
    have hxnorm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
    have hrelative :
        vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
          ((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus +
            eta ^ 2 *
              (higham21Eq21_11UniformAbsoluteCoefficient A b rho /
                vecNorm2 x) := by
      calc
        vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
            ((((m + k : Nat) : Real) * eta *
                  higham21Cond2With A Aplus * vecNorm2 x) +
                eta ^ 2 * higham21Eq21_11UniformAbsoluteCoefficient A b rho) /
              vecNorm2 x :=
          div_le_div_of_nonneg_right habsolute (le_of_lt hxnorm_pos)
        _ = ((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus +
            eta ^ 2 *
              (higham21Eq21_11UniformAbsoluteCoefficient A b rho /
                vecNorm2 x) := by
          field_simp [hxnorm_ne]
    simpa [higham21Eq21_11UniformRelativeCoefficient, Aplus, x, eta] using
      hrelative

end NumStability
