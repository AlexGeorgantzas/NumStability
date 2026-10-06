-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A derived fixed-radius neighborhood for Theorem 21.1 and equation (21.6).

import NumStability.Algorithms.Underdetermined.Higham21Perturbation

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The exact Euclidean operator norm of a real rectangular matrix, routed
    through the operator norm of its complexification.  The real/complex
    bridge in `Norms.lean` shows that this is also the sharp radius for the
    repository predicate `rectOpNorm2Le`. -/
noncomputable def higham21RectOpNorm2 {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A)

theorem higham21RectOpNorm2_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21RectOpNorm2 A := by
  exact complexMatrixOp2_nonneg _

/-- The exact rectangular condition-number product associated with a supplied
    pseudoinverse.  For the Moore--Penrose inverse this is Higham's
    `kappa_2(A) = ||A||_2 ||A^+||_2`. -/
noncomputable def higham21RectKappa2With {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) : Real :=
  higham21RectOpNorm2 A * higham21RectOpNorm2 Aplus

theorem higham21RectKappa2With_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) :
    0 <= higham21RectKappa2With A Aplus := by
  exact mul_nonneg (higham21RectOpNorm2_nonneg A)
    (higham21RectOpNorm2_nonneg Aplus)

/-- The exact rectangular norm is an admissible vector-action certificate. -/
theorem higham21_rectOpNorm2Le_exact {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    rectOpNorm2Le A (higham21RectOpNorm2 A) := by
  exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl

/-- Conversely, every nonnegative vector-action certificate bounds the exact
    rectangular operator norm. -/
theorem higham21RectOpNorm2_le_of_rectOpNorm2Le {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real}
    (hc : 0 <= c) (hA : rectOpNorm2Le A c) :
    higham21RectOpNorm2 A <= c := by
  exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A hc hA

/-- A fixed Gram-perturbation envelope for directions satisfying `abs D <= E`.
    The quadratic part is frozen at unit radius, so every smaller signed
    perturbation has a Gram perturbation bounded by `abs t` times this table. -/
noncomputable def higham21PerturbationGramEnvelope {m n : Nat}
    (A E : Fin m -> Fin n -> Real) : Fin m -> Fin m -> Real :=
  undetGramPerturbationComponentBudget A E 1

/-- Chapter 7 sensitivity of the fixed Gram envelope. -/
noncomputable def higham21PerturbationGramSensitivity {m n : Nat}
    (A E : Fin m -> Fin n -> Real) : Real :=
  infNorm
    (ch7InverseFirstProductSensitivity m (undetGramNonsingInv A)
      (higham21PerturbationGramEnvelope A E))

/-- A positive radius that simultaneously controls a supplied operator bound
    `q` for `A^+ D` and the fixed Gram-envelope sensitivity.  The factor two
    leaves a half-radius margin for both contractions. -/
noncomputable def higham21PerturbationRadius {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) : Real :=
  1 /
    (2 *
      (1 + max q (higham21PerturbationGramSensitivity A E)))

/-- A direction-independent inverse bound once the Gram contraction is at
    most `1/2`. -/
noncomputable def higham21PerturbationGramInverseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  Real.sqrt ((m : Real) * (m : Real)) *
    (((m : Real) * 2) * infNorm (undetGramNonsingInv A))

/-- A pointwise envelope induced by row 2-norm bounds. -/
def higham21PerturbationEntryEnvelopeOfRow {m n : Nat}
    (r : Fin m -> Real) : Fin m -> Fin n -> Real :=
  fun i _ => r i

/-- A canonical finite operator envelope for one perturbation direction. -/
noncomputable def higham21PerturbationDirectionProductBound {m n : Nat}
    (A D : Fin m -> Fin n -> Real) : Real :=
  frobNorm
    (rectMatMul (undetAplusOfGramNonsingInv A) D)

/-- The single-direction radius obtained without any caller-supplied norm
    constant. -/
noncomputable def higham21PerturbationDirectionRadius {m n : Nat}
    (A D E : Fin m -> Fin n -> Real) : Real :=
  higham21PerturbationRadius A E
    (higham21PerturbationDirectionProductBound A D)

theorem higham21PerturbationGramSensitivity_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) :
    0 <= higham21PerturbationGramSensitivity A E :=
  infNorm_nonneg _

private theorem higham21PerturbationRadius_mul_max_le_half {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    higham21PerturbationRadius A E q *
        max q (higham21PerturbationGramSensitivity A E) <=
      (1 / 2 : Real) := by
  let s : Real := higham21PerturbationGramSensitivity A E
  let M : Real := max q s
  have hM : 0 <= M := by
    exact hq.trans (le_max_left q s)
  have hden : 0 < 2 * (1 + M) :=
    mul_pos (by norm_num) (by linarith)
  have hfrac : M / (2 * (1 + M)) <= (1 / 2 : Real) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  change (1 / (2 * (1 + M))) * M <= (1 / 2 : Real)
  simpa [div_eq_mul_inv, mul_comm] using hfrac

/-- The derived radius is strictly positive for every nonnegative operator
    envelope. -/
theorem higham21PerturbationRadius_pos {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    0 < higham21PerturbationRadius A E q := by
  let s : Real := higham21PerturbationGramSensitivity A E
  let M : Real := max q s
  have hM : 0 <= M := by
    exact hq.trans (le_max_left q s)
  have hden : 0 < 2 * (1 + M) :=
    mul_pos (by norm_num) (by linarith)
  change 0 < 1 / (2 * (1 + M))
  exact one_div_pos.mpr hden

/-- The derived radius lies inside the unit neighborhood used to freeze the
    quadratic Gram envelope. -/
theorem higham21PerturbationRadius_le_one {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    higham21PerturbationRadius A E q <= 1 := by
  let s : Real := higham21PerturbationGramSensitivity A E
  let M : Real := max q s
  have hM : 0 <= M := by
    exact hq.trans (le_max_left q s)
  have hden : 0 < 2 * (1 + M) :=
    mul_pos (by norm_num) (by linarith)
  change 1 / (2 * (1 + M)) <= 1
  apply (div_le_iff₀ hden).2
  nlinarith

/-- At the derived radius the printed pseudoinverse-product envelope is at
    most one half. -/
theorem higham21PerturbationRadius_mul_product_le_half {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    higham21PerturbationRadius A E q * q <= (1 / 2 : Real) := by
  have hrho : 0 <= higham21PerturbationRadius A E q :=
    (higham21PerturbationRadius_pos A E q hq).le
  calc
    higham21PerturbationRadius A E q * q <=
        higham21PerturbationRadius A E q *
          max q (higham21PerturbationGramSensitivity A E) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hrho
    _ <= (1 / 2 : Real) :=
      higham21PerturbationRadius_mul_max_le_half A E q hq

/-- At the same radius the Chapter 7 Gram contraction is at most one half. -/
theorem higham21PerturbationRadius_mul_gramSensitivity_le_half {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    higham21PerturbationRadius A E q *
        higham21PerturbationGramSensitivity A E <=
      (1 / 2 : Real) := by
  have hrho : 0 <= higham21PerturbationRadius A E q :=
    (higham21PerturbationRadius_pos A E q hq).le
  calc
    higham21PerturbationRadius A E q *
        higham21PerturbationGramSensitivity A E <=
      higham21PerturbationRadius A E q *
        max q (higham21PerturbationGramSensitivity A E) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hrho
    _ <= (1 / 2 : Real) :=
      higham21PerturbationRadius_mul_max_le_half A E q hq

theorem higham21PerturbationGramInverseBound_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21PerturbationGramInverseBound A := by
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le m) (by norm_num))
      (infNorm_nonneg _))

/-- The canonical Frobenius product bound is an operator-2 certificate. -/
theorem higham21PerturbationDirectionProduct_rectOpNorm2Le {m n : Nat}
    (A D : Fin m -> Fin n -> Real) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A) D)
      (higham21PerturbationDirectionProductBound A D) := by
  exact
    rectOpNorm2Le_of_opNorm2Le_square _
      (opNorm2Le_of_frobNorm_self _)

theorem higham21PerturbationDirectionRadius_pos {m n : Nat}
    (A D E : Fin m -> Fin n -> Real) :
    0 < higham21PerturbationDirectionRadius A D E := by
  simpa [higham21PerturbationDirectionRadius] using
    higham21PerturbationRadius_pos A E
      (higham21PerturbationDirectionProductBound A D)
      (frobNorm_nonneg _)

/-- Monotonicity of the componentwise Gram budget in its scalar quadratic
    radius. -/
theorem higham21_undetGramPerturbationComponentBudget_mono {m n : Nat}
    (A E : Fin m -> Fin n -> Real) {r s : Real}
    (hE : forall i j, 0 <= E i j) (hrs : r <= s) :
    forall i j,
      undetGramPerturbationComponentBudget A E r i j <=
        undetGramPerturbationComponentBudget A E s i j := by
  intro i j
  unfold undetGramPerturbationComponentBudget
  apply Finset.sum_le_sum
  intro k _
  have hquad : r * (E i k * E j k) <= s * (E i k * E j k) :=
    mul_le_mul_of_nonneg_right hrs (mul_nonneg (hE i k) (hE j k))
  exact add_le_add le_rfl (by simpa [mul_assoc] using hquad)

/-- Scalar multiplication scales a rectangular operator-2 certificate by the
    absolute value of the scalar. -/
theorem higham21_rectOpNorm2Le_const_mul_abs {m n : Nat}
    (M : Fin m -> Fin n -> Real) (a c : Real)
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => a * M i j) (abs a * c) := by
  intro x
  have haction :
      rectMatMulVec (fun i j => a * M i j) x =
        fun i => a * rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    vecNorm2 (rectMatMulVec (fun i j => a * M i j) x) =
        abs a * vecNorm2 (rectMatMulVec M x) := by
      rw [haction, vecNorm2_smul]
    _ <= abs a * (c * vecNorm2 x) :=
      mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)
    _ = (abs a * c) * vecNorm2 x := by ring

/-- Scaling a direction scales its canonical pseudoinverse product
    certificate. -/
theorem higham21_scaled_pseudoinverse_product_rectOpNorm2Le {m n : Nat}
    (A D : Fin m -> Fin n -> Real) (t q : Real)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) D) q) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A)
        (fun i j => t * D i j))
      (abs t * q) := by
  have hscaled :=
    higham21_rectOpNorm2Le_const_mul_abs
      (rectMatMul (undetAplusOfGramNonsingInv A) D) t q hProduct
  have hmul :
      rectMatMul (undetAplusOfGramNonsingInv A)
          (fun i j => t * D i j) =
        fun i j =>
          t * rectMatMul (undetAplusOfGramNonsingInv A) D i j := by
    ext i j
    unfold rectMatMul
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hmul]
  exact hscaled

/-- Inside the derived radius, the printed contraction
    `norm (A^+ (t D)) < 1` follows from a fixed operator envelope for
    `A^+ D`. -/
theorem higham21_theorem21_1_scaled_product_contraction_of_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real) (q t : Real)
    (hq : 0 <= q)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) D) q)
    (ht : abs t <= higham21PerturbationRadius A E q) :
    rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A)
          (fun i j => t * D i j))
        (abs t * q) /\
      abs t * q < 1 := by
  have hhalf : abs t * q <= (1 / 2 : Real) :=
    (mul_le_mul_of_nonneg_right ht hq).trans
      (higham21PerturbationRadius_mul_product_le_half A E q hq)
  constructor
  · exact higham21_scaled_pseudoinverse_product_rectOpNorm2Le
      A D t q hProduct
  · exact hhalf.trans_lt (by norm_num)

/-- Full row rank is preserved throughout the derived signed radius. -/
theorem higham21_theorem21_1_scaled_gram_det_ne_zero_of_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real) (q t : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hq : 0 <= q)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) D) q)
    (ht : abs t <= higham21PerturbationRadius A E q) :
    Not
      (Matrix.det
        (rectGram (higham21Eq21_7ScaledMatrix A D t) :
          Matrix (Fin m) (Fin m) Real) = 0) := by
  have hcontract :=
    higham21_theorem21_1_scaled_product_contraction_of_radius
      A D E q t hq hProduct ht
  simpa only [higham21Eq21_7ScaledMatrix] using
    higham21_theorem21_1_perturbed_gram_det_ne_zero_of_gram_det_ne_zero
      A (fun i j => t * D i j) hdet hcontract.1
      (mul_nonneg (abs_nonneg t) hq) hcontract.2

/-- The perturbed Gram inverse has one Frobenius bound for every signed
    parameter in the derived radius. -/
theorem higham21_theorem21_1_scaled_gramInverse_frobNorm_le_of_radius
    {m n : Nat} (A D E : Fin m -> Fin n -> Real) (q t : Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hq : 0 <= q)
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, abs (D i j) <= E i j)
    (ht : abs t <= higham21PerturbationRadius A E q) :
    frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A D t)) <=
      higham21PerturbationGramInverseBound A := by
  let eta : Real := abs t
  let Delta : Fin m -> Fin n -> Real := fun i j => t * D i j
  let F : Fin m -> Fin m -> Real :=
    higham21PerturbationGramEnvelope A E
  let G : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let s : Real := higham21PerturbationGramSensitivity A E
  let c : Real := eta * s
  have heta : 0 <= eta := by
    simpa [eta] using abs_nonneg t
  have heta_rho : eta <= higham21PerturbationRadius A E q := by
    simpa [eta] using ht
  have heta_one : eta <= 1 :=
    heta_rho.trans (higham21PerturbationRadius_le_one A E q hq)
  have hDelta : forall i j, abs (Delta i j) <= eta * E i j := by
    intro i j
    calc
      abs (Delta i j) = eta * abs (D i j) := by
        simp [Delta, eta, abs_mul]
      _ <= eta * E i j :=
        mul_le_mul_of_nonneg_left (hD i j) heta
  have hF : forall i j, 0 <= F i j := by
    simpa [F, higham21PerturbationGramEnvelope] using
      (undetGramPerturbationComponentBudget_nonneg A E
        (eps := (1 : Real)) (by norm_num) hE)
  have hBudget : forall i j,
      undetGramPerturbationComponentBudget A E eta i j <= F i j := by
    intro i j
    simpa [F, higham21PerturbationGramEnvelope] using
      (higham21_undetGramPerturbationComponentBudget_mono
        A E (r := eta) (s := (1 : Real)) hE heta_one i j)
  have hDeltaG : forall i j,
      abs (undetGramPerturbation A Delta i j) <= eta * F i j := by
    intro i j
    calc
      abs (undetGramPerturbation A Delta i j) <=
          eta * undetGramPerturbationComponentBudget A E eta i j :=
        undetGramPerturbation_abs_le_componentBudget
          A Delta E heta hE hDelta i j
      _ <= eta * F i j :=
        mul_le_mul_of_nonneg_left (hBudget i j) heta
  have hs : 0 <= s := by
    simpa [s] using higham21PerturbationGramSensitivity_nonneg A E
  have hc : 0 <= c := mul_nonneg heta hs
  have hc_half : c <= (1 / 2 : Real) := by
    calc
      c = eta * higham21PerturbationGramSensitivity A E := by
        rfl
      _ <= higham21PerturbationRadius A E q *
          higham21PerturbationGramSensitivity A E :=
        mul_le_mul_of_nonneg_right heta_rho
          (higham21PerturbationGramSensitivity_nonneg A E)
      _ <= (1 / 2 : Real) :=
        higham21PerturbationRadius_mul_gramSensitivity_le_half A E q hq
  have hc_lt : c < 1 := hc_half.trans_lt (by norm_num)
  have hLeft : IsLeftInverse m (rectGram A) G := by
    simpa [G, undetGramNonsingInv] using
      (isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet).1
  have hbound :
      infNormBound m
        (absMatrix m
          (matMul m G (undetGramPerturbation A Delta))) c := by
    simpa [c, s, F, G, higham21PerturbationGramSensitivity,
      higham21PerturbationGramEnvelope] using
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A Delta G F eta heta hF hDeltaG
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
          (((m : Real) * 2) * infNorm G) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_half_radius
      hm G (undetGramPerturbation A Delta) c hc hc_half hbound
  have hscaled :
      higham21Eq21_7ScaledMatrix A D t =
        fun i j => A i j + Delta i j := by
    rfl
  rw [hscaled, hInvEq]
  simpa [higham21PerturbationGramInverseBound, G] using hCandidate

/-- A single fixed operator envelope and entrywise direction envelope produce
    all local determinant and inverse certificates needed by finite-error
    perturbation theorems. -/
theorem higham21_theorem21_1_fixed_radius_certificates_of_product_and_entrywise_envelopes
    {m n : Nat} (A D E : Fin m -> Fin n -> Real) (q : Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hq : 0 <= q)
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, abs (D i j) <= E i j)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) D) q) :
    0 < higham21PerturbationRadius A E q /\
      0 <= higham21PerturbationGramInverseBound A /\
      forall t, abs t <= higham21PerturbationRadius A E q ->
        Not
            (Matrix.det
              (rectGram (higham21Eq21_7ScaledMatrix A D t) :
                Matrix (Fin m) (Fin m) Real) = 0) /\
          frobNorm
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A D t)) <=
            higham21PerturbationGramInverseBound A := by
  constructor
  · exact higham21PerturbationRadius_pos A E q hq
  constructor
  · exact higham21PerturbationGramInverseBound_nonneg A
  · intro t ht
    constructor
    · exact higham21_theorem21_1_scaled_gram_det_ne_zero_of_radius
        A D E q t hdet hq hProduct ht
    · exact higham21_theorem21_1_scaled_gramInverse_frobNorm_le_of_radius
        A D E q t hm hdet hq hE hD ht

/-- The canonical Frobenius product certificate removes even the local
    operator-envelope premise for a single normalized direction. -/
theorem higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
    {m n : Nat} (A D E : Fin m -> Fin n -> Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, abs (D i j) <= E i j) :
    0 < higham21PerturbationDirectionRadius A D E /\
      0 <= higham21PerturbationGramInverseBound A /\
      forall t, abs t <= higham21PerturbationDirectionRadius A D E ->
        Not
            (Matrix.det
              (rectGram (higham21Eq21_7ScaledMatrix A D t) :
                Matrix (Fin m) (Fin m) Real) = 0) /\
          frobNorm
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A D t)) <=
            higham21PerturbationGramInverseBound A := by
  simpa [higham21PerturbationDirectionRadius] using
    (higham21_theorem21_1_fixed_radius_certificates_of_product_and_entrywise_envelopes
      A D E (higham21PerturbationDirectionProductBound A D)
      hm hdet (frobNorm_nonneg _) hE hD
      (higham21PerturbationDirectionProduct_rectOpNorm2Le A D))

/-- Composition of operator envelopes gives the fixed product envelope used
    by the family-radius API. -/
theorem higham21_theorem21_1_product_rectOpNorm2Le_of_operator_envelopes
    {m n : Nat} (A D : Fin m -> Fin n -> Real) (p d : Real)
    (hp : 0 <= p)
    (hAplus :
      rectOpNorm2Le (undetAplusOfGramNonsingInv A) p)
    (hD : rectOpNorm2Le D d) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A) D) (p * d) :=
  rectOpNorm2Le_rectMatMul
    (undetAplusOfGramNonsingInv A) D hp hAplus hD

/-- An entrywise direction envelope plus an operator certificate for that
    envelope supplies the product certificate required by the family API. -/
theorem higham21_theorem21_1_product_rectOpNorm2Le_of_entrywise_operator_envelopes
    {m n : Nat} (A D E : Fin m -> Fin n -> Real) (p e : Real)
    (hp : 0 <= p)
    (hAplus :
      rectOpNorm2Le (undetAplusOfGramNonsingInv A) p)
    (hEop : rectOpNorm2Le E e)
    (hD : forall i j, abs (D i j) <= E i j) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A) D) (p * e) := by
  have hDone : forall i j, abs (D i j) <= (1 : Real) * E i j := by
    intro i j
    simpa using hD i j
  have hDop : rectOpNorm2Le D ((1 : Real) * e) :=
    higham21_rectOpNorm2Le_of_componentwise_data_bound
      D E (eps := (1 : Real)) (e := e) (by norm_num) hDone hEop
  exact higham21_theorem21_1_product_rectOpNorm2Le_of_operator_envelopes
    A D p e hp hAplus (by simpa using hDop)

theorem higham21PerturbationEntryEnvelopeOfRow_nonneg {m n : Nat}
    (r : Fin m -> Real) (hr : forall i, 0 <= r i) :
    forall i j, 0 <= higham21PerturbationEntryEnvelopeOfRow
      (n := n) r i j := by
  intro i j
  exact hr i

/-- A row 2-norm envelope induces the pointwise envelope used in the Gram
    budget. -/
theorem higham21_abs_entry_le_entryEnvelopeOfRow {m n : Nat}
    (D : Fin m -> Fin n -> Real) (r : Fin m -> Real)
    (hrow : forall i, rectRowNorm2 D i <= r i) :
    forall i j, abs (D i j) <=
      higham21PerturbationEntryEnvelopeOfRow r i j := by
  intro i j
  calc
    abs (D i j) <= rectRowNorm2 D i := by
      simpa [rectRowNorm2] using
        (abs_coord_le_vecNorm2 (fun k : Fin n => D i k) j)
    _ <= r i := hrow i
    _ = higham21PerturbationEntryEnvelopeOfRow r i j := rfl

/-- One fixed entrywise and pseudoinverse-product envelope controls every
    member of a perturbation family.  This is the adapter for downstream
    bounds whose normalized direction is selected existentially. -/
theorem higham21_theorem21_1_fixed_radius_certificates_of_family_entrywise_envelope
    {iota : Type*} {m n : Nat}
    (A E : Fin m -> Fin n -> Real)
    (D : iota -> Fin m -> Fin n -> Real) (q : Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hq : 0 <= q)
    (hE : forall i j, 0 <= E i j)
    (hD : forall a i j, abs (D a i j) <= E i j)
    (hProduct : forall a,
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) (D a)) q) :
    0 < higham21PerturbationRadius A E q /\
      0 <= higham21PerturbationGramInverseBound A /\
      forall a t, abs t <= higham21PerturbationRadius A E q ->
        Not
            (Matrix.det
              (rectGram (higham21Eq21_7ScaledMatrix A (D a) t) :
                Matrix (Fin m) (Fin m) Real) = 0) /\
          frobNorm
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A (D a) t)) <=
            higham21PerturbationGramInverseBound A := by
  constructor
  · exact higham21PerturbationRadius_pos A E q hq
  constructor
  · exact higham21PerturbationGramInverseBound_nonneg A
  · intro a t ht
    constructor
    · exact higham21_theorem21_1_scaled_gram_det_ne_zero_of_radius
        A (D a) E q t hdet hq (hProduct a) ht
    · exact higham21_theorem21_1_scaled_gramInverse_frobNorm_le_of_radius
        A (D a) E q t hm hdet hq hE (hD a) ht

/-- Rowwise family adapter: a fixed row envelope and fixed operator envelope
    imply the same determinant and inverse certificates for every family
    member. -/
theorem higham21_theorem21_1_fixed_radius_certificates_of_family_row_envelope
    {iota : Type*} {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (D : iota -> Fin m -> Fin n -> Real)
    (r : Fin m -> Real) (q : Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hq : 0 <= q)
    (hr : forall i, 0 <= r i)
    (hrow : forall a i, rectRowNorm2 (D a) i <= r i)
    (hProduct : forall a,
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) (D a)) q) :
    0 < higham21PerturbationRadius A
          (higham21PerturbationEntryEnvelopeOfRow r) q /\
      0 <= higham21PerturbationGramInverseBound A /\
      forall a t,
        abs t <= higham21PerturbationRadius A
          (higham21PerturbationEntryEnvelopeOfRow r) q ->
        Not
            (Matrix.det
              (rectGram (higham21Eq21_7ScaledMatrix A (D a) t) :
                Matrix (Fin m) (Fin m) Real) = 0) /\
          frobNorm
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A (D a) t)) <=
            higham21PerturbationGramInverseBound A := by
  exact
    higham21_theorem21_1_fixed_radius_certificates_of_family_entrywise_envelope
      A (higham21PerturbationEntryEnvelopeOfRow r) D q hm hdet hq
      (higham21PerturbationEntryEnvelopeOfRow_nonneg r hr)
      (fun a => higham21_abs_entry_le_entryEnvelopeOfRow
        (D a) r (hrow a))
      hProduct

/-- A nonzero right-hand side forces a positive row dimension. -/
theorem higham21_row_dimension_pos_of_rhs_ne_zero {m : Nat}
    (b : Fin m -> Real) (hb : Not (b = 0)) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  apply hb
  funext i
  exact Fin.elim0 i

/-- The finite relative Theorem 21.1 bound with its perturbed determinant and
    Gram-inverse hypotheses derived from the normalized direction itself. -/
theorem higham21_theorem21_1_finite_error_relative_bound_of_direction_envelope
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A D E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (t : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hD : forall i j, abs (D i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i)
    (ht : abs t <= higham21PerturbationDirectionRadius A D E) :
    nu (realVecToComplex
        (fun j =>
          higham21Eq21_7PerturbedSolution A D b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A D t)) t j -
            higham21Eq21_7BaseSolution A b
              (undetGramNonsingInv A) j)) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) <=
      (abs t *
            (nu (realVecToComplex
                (higham21Theorem21_1NullspaceMajorant A E b)) +
              nu (realVecToComplex
                (higham21Theorem21_1DataMajorant A E b f))) +
          abs t ^ 2 *
            (higham21Eq21_7FixedRadiusCoefficient A D b Deltab
                  (undetGramNonsingInv A)
                  (higham21PerturbationDirectionRadius A D E)
                  (higham21PerturbationGramInverseBound A) *
              nu (realVecToComplex (fun _ : Fin n => (1 : Real))))) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) := by
  have hm : 0 < m := higham21_row_dimension_pos_of_rhs_ne_zero b hb
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  have htcert := hcert.2.2 t ht
  exact
    higham21_theorem21_1_finite_error_relative_bound_of_gram_det_ne_zero
      nu hnu habs A D E b Deltab f
      (higham21PerturbationDirectionRadius A D E)
      (higham21PerturbationGramInverseBound A) t
      hdet htcert.1 hb hE hf hD hDeltab
      hcert.1.le hcert.2.1 ht htcert.2

/-- The normalized absolute-norm remainder in Theorem 21.1 is `O(t^2)` on
    the derived neighborhood, with no local inverse hypothesis left to the
    caller. -/
theorem higham21_theorem21_1_relative_remainder_isBigO_of_direction_envelope
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A D E : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, abs (D i j) <= E i j) :
    (fun t =>
      nu (realVecToComplex
          (higham21Eq21_7ExactRemainder A D b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D t)) t)) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b))) =O[nhds 0]
      (fun t : Real => t ^ 2) := by
  have hm : 0 < m := higham21_row_dimension_pos_of_rhs_ne_zero b hb
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  have hRemainderO :
      (fun t =>
        nu (realVecToComplex
          (higham21Eq21_7ExactRemainder A D b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D t)) t))) =O[nhds 0]
        (fun t : Real => t ^ 2) :=
    higham21Eq21_7_exactRemainder_absoluteNorm_isBigO
      nu hnu habs A D b Deltab (undetGramNonsingInv A)
      (fun t =>
        undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D t))
      (higham21PerturbationDirectionRadius A D E)
      (higham21PerturbationGramInverseBound A)
      hcert.1 hcert.2.1 (fun t ht => (hcert.2.2 t ht).2)
  have hNormalized :=
    hRemainderO.const_mul_left
      (Inv.inv
        (nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b))))
  simpa only [div_eq_mul_inv, mul_comm] using hNormalized

/-- Higham's Theorem 21.1, equation (21.6), in an arbitrary absolute norm.
    The displayed relative remainder is `O(t^2)`, and every determinant and
    inverse estimate used to justify that statement is derived from full row
    rank and the normalized direction envelope. -/
theorem higham21_theorem21_1_relative_asymptotic_bound_of_direction_envelope
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A D E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hD : forall i j, abs (D i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i) :
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let remainderRatio : Real -> Real := fun t =>
      nu (realVecToComplex
          (higham21Eq21_7ExactRemainder A D b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D t)) t)) /
        nu (realVecToComplex x)
    And
      (remainderRatio =O[nhds 0] (fun t : Real => t ^ 2))
      (forall t,
        abs t <= higham21PerturbationDirectionRadius A D E ->
        nu (realVecToComplex
            (fun j =>
              higham21Eq21_7PerturbedSolution A D b Deltab
                    (undetGramNonsingInv
                      (higham21Eq21_7ScaledMatrix A D t)) t j -
                higham21Eq21_7BaseSolution A b
                  (undetGramNonsingInv A) j)) /
            nu (realVecToComplex x) <=
          abs t *
              ((nu (realVecToComplex
                    (higham21Theorem21_1NullspaceMajorant A E b)) +
                  nu (realVecToComplex
                    (higham21Theorem21_1DataMajorant A E b f))) /
                nu (realVecToComplex x)) +
            remainderRatio t) := by
  have hm : 0 < m := higham21_row_dimension_pos_of_rhs_ne_zero b hb
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  exact
    higham21_theorem21_1_relative_asymptotic_bound_of_gram_det_ne_zero
      nu hnu habs A D E b Deltab f
      (higham21PerturbationDirectionRadius A D E)
      (higham21PerturbationGramInverseBound A)
      hdet (fun t ht => (hcert.2.2 t ht).1) hb hE hf hD hDeltab
      hcert.1 hcert.2.1 (fun t ht => (hcert.2.2 t ht).2)

/-- Euclidean specialization of the exact equation-(21.7) expansion with an
    arbitrary proved first-order coefficient.  The result packages the actual
    normalized remainder as an `O(t^2)` function, rather than merely replacing
    it by a pointwise quadratic majorant.  Equations (21.8) and (21.9) are
    obtained by supplying their respective first-order estimates. -/
theorem higham21_eq21_7_euclidean_relative_asymptotic_bound_of_firstOrder_bound
    {m n : Nat}
    (A D E : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (K : Real)
    (hm : 0 < m)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hE : forall i j, 0 <= E i j)
    (hD : forall i j, abs (D i j) <= E i j)
    (hxpos :
      0 < vecNorm2
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b))
    (hfirst :
      vecNorm2
          (higham21Eq21_7FirstOrder A D b Deltab
            (undetGramNonsingInv A)) <=
        K * vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) :
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let remainderRatio : Real -> Real := fun t =>
      vecNorm2
          (higham21Eq21_7ExactRemainder A D b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D t)) t) /
        vecNorm2 x
    And
      (remainderRatio =O[nhds 0] (fun t : Real => t ^ 2))
      (forall t,
        abs t <= higham21PerturbationDirectionRadius A D E ->
        vecNorm2
            (fun j =>
              higham21Eq21_7PerturbedSolution A D b Deltab
                    (undetGramNonsingInv
                      (higham21Eq21_7ScaledMatrix A D t)) t j -
                higham21Eq21_7BaseSolution A b
                  (undetGramNonsingInv A) j) /
            vecNorm2 x <=
          abs t * K + remainderRatio t) := by
  dsimp only
  let x : Fin n -> Real :=
    rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let firstOrder : Fin n -> Real :=
    higham21Eq21_7FirstOrder A D b Deltab
      (undetGramNonsingInv A)
  let remainder : Real -> Fin n -> Real := fun t =>
    higham21Eq21_7ExactRemainder A D b Deltab
      (undetGramNonsingInv A)
      (undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D t)) t
  have hcert :=
    higham21_theorem21_1_fixed_radius_certificates_of_direction_envelope
      A D E hm hdet hE hD
  constructor
  · have hO :
        (fun t => vecNorm2 (remainder t)) =O[nhds 0]
          (fun t : Real => t ^ 2) := by
      simpa [remainder] using
        (higham21Eq21_7_exactRemainder_vecNorm2_isBigO
          A D b Deltab (undetGramNonsingInv A)
          (fun t =>
            undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D t))
          (higham21PerturbationDirectionRadius A D E)
          (higham21PerturbationGramInverseBound A)
          hcert.1 hcert.2.1 (fun t ht => (hcert.2.2 t ht).2))
    have hNormalized := hO.const_mul_left (vecNorm2 x)⁻¹
    simpa [x, remainder, div_eq_mul_inv, mul_comm] using hNormalized
  · intro t ht
    have hdet_t := (hcert.2.2 t ht).1
    have hscaled :
        vecNorm2 (fun j => t * firstOrder j) / vecNorm2 x <=
          abs t * K := by
      have hfirst' : vecNorm2 firstOrder <= K * vecNorm2 x := by
        simpa [firstOrder, x] using hfirst
      have hmul :
          abs t * vecNorm2 firstOrder <=
            abs t * (K * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hfirst' (abs_nonneg t)
      rw [vecNorm2_smul]
      calc
        abs t * vecNorm2 firstOrder / vecNorm2 x <=
            (abs t * (K * vecNorm2 x)) / vecNorm2 x :=
          div_le_div_of_nonneg_right hmul hxpos.le
        _ = abs t * K := by
           simp only [div_eq_mul_inv]
           have hxne : vecNorm2 x ≠ 0 := by
             simpa [x] using (ne_of_gt hxpos)
           calc
             abs t * (K * vecNorm2 x) * (vecNorm2 x)⁻¹ =
                 (abs t * K) * (vecNorm2 x * (vecNorm2 x)⁻¹) := by ring
             _ = abs t * K := by rw [mul_inv_cancel₀ hxne, mul_one]
    have hExpansion :=
      higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
        A D b Deltab t hdet hdet_t
    rw [hExpansion]
    change
      vecNorm2 (fun j => t * firstOrder j + remainder t j) /
          vecNorm2 x <=
        abs t * K + vecNorm2 (remainder t) / vecNorm2 x
    calc
      vecNorm2 (fun j => t * firstOrder j + remainder t j) /
            vecNorm2 x <=
          (vecNorm2 (fun j => t * firstOrder j) +
              vecNorm2 (remainder t)) / vecNorm2 x :=
        div_le_div_of_nonneg_right
          (vecNorm2_add_le (fun j => t * firstOrder j) (remainder t))
          hxpos.le
      _ = vecNorm2 (fun j => t * firstOrder j) / vecNorm2 x +
          vecNorm2 (remainder t) / vecNorm2 x := by ring
      _ <= abs t * K + vecNorm2 (remainder t) / vecNorm2 x :=
        add_le_add hscaled le_rfl

end NumStability
