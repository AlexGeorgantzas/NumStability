import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.Radius
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.Radius
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.FixedRadius.Radius
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.Radius

/-!
# Algorithms.Underdetermined.Higham21PerturbationRadius

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A derived fixed-radius neighborhood for Theorem 21.1 and equation (21.6).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius
































































































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
