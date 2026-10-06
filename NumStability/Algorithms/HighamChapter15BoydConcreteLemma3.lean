-- Algorithms/HighamChapter15BoydConcreteLemma3.lean
--
-- Concrete weighted geometry behind Boyd's corrected Lemma 3.  The source
-- theorem is valid at a nondegenerate constrained stationary point; an
-- ordinary strict maximum is not enough (see `strictMaximum_does_not_imply_\
-- negative_quadratic_term` in the imported source-local module).

import NumStability.Algorithms.HighamChapter15BoydSourceLocal

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

/-- The tangent hyperplane to the `p`-unit sphere at `x`, written in Boyd's
weighted pairing. -/
def boydConcreteTangent {n : ℕ} (p : ℝ) (x : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) where
  carrier := {h | boydWeightedPair p x x h = 0}
  zero_mem' := by simp [boydWeightedPair]
  add_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    have hg' : (∑ i, |x i| ^ (p - 2) * x i * g i) = 0 := by
      simpa [boydWeightedPair] using hg
    have hh' : (∑ i, |x i| ^ (p - 2) * x i * h i) = 0 := by
      simpa [boydWeightedPair] using hh
    simp only [boydWeightedPair, Pi.add_apply]
    calc
      (∑ i, |x i| ^ (p - 2) * x i * (g i + h i)) =
          (∑ i, |x i| ^ (p - 2) * x i * g i) +
            ∑ i, |x i| ^ (p - 2) * x i * h i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hg', hh', zero_add]
  smul_mem' := by
    intro a h hh
    simp only [Set.mem_setOf_eq] at hh ⊢
    have hh' : (∑ i, |x i| ^ (p - 2) * x i * h i) = 0 := by
      simpa [boydWeightedPair] using hh
    simp only [boydWeightedPair, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, |x i| ^ (p - 2) * x i * (a * h i)) =
          a * ∑ i, |x i| ^ (p - 2) * x i * h i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hh', mul_zero]

@[simp] theorem mem_boydConcreteTangent {n : ℕ} {p : ℝ}
    {x h : Fin n → ℝ} :
    h ∈ boydConcreteTangent p x ↔ boydWeightedPair p x x h = 0 :=
  Iff.rfl

/-- Diagonal square-root scaling that transports Boyd's weighted pairing to
the ordinary Euclidean inner product. -/
noncomputable def boydWeightScaleEquiv {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun h := fun i => Real.sqrt (|x i| ^ (p - 2)) * h i
  invFun h := fun i => (Real.sqrt (|x i| ^ (p - 2)))⁻¹ * h i
  left_inv h := by
    funext i
    have hw : 0 < |x i| ^ (p - 2) :=
      Real.rpow_pos_of_pos (abs_pos.mpr (hxcoord i)) _
    have hs : Real.sqrt (|x i| ^ (p - 2)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hw)
    simp [hs]
  right_inv h := by
    funext i
    have hw : 0 < |x i| ^ (p - 2) :=
      Real.rpow_pos_of_pos (abs_pos.mpr (hxcoord i)) _
    have hs : Real.sqrt (|x i| ^ (p - 2)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hw)
    field_simp
  map_add' g h := by
    funext i
    simp [mul_add]
  map_smul' a h := by
    funext i
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- The preceding finite-dimensional linear equivalence is continuous. -/
noncomputable def boydWeightScaleContinuousEquiv {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (boydWeightScaleEquiv p x hxcoord).toContinuousLinearEquiv

/-- Square-root scaling with Euclidean codomain. -/
noncomputable def boydWeightEuclideanEquiv {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (boydWeightScaleContinuousEquiv p x hxcoord).trans
    (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem boydWeightEuclideanEquiv_apply {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) (i : Fin n) :
    boydWeightEuclideanEquiv p x hxcoord h i =
      Real.sqrt (|x i| ^ (p - 2)) * h i :=
  rfl

/-- The Hilbert tangent model obtained by square-root diagonal scaling. -/
noncomputable def boydScaledTangent {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (boydConcreteTangent p x).map
    (boydWeightEuclideanEquiv p x hxcoord).toLinearMap

/-- Continuous equivalence from the scaled Euclidean tangent model back to
the original tangent hyperplane. -/
noncomputable def boydScaledTangentEquiv {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    boydScaledTangent p x hxcoord ≃L[ℝ] boydConcreteTangent p x :=
  ((boydWeightEuclideanEquiv p x hxcoord).toLinearEquiv.submoduleMap
    (boydConcreteTangent p x)).symm.toContinuousLinearEquiv

/-- The positive operator in Boyd's Lemma 3.  At a stationary point it is
the actual derivative on the tangent hyperplane. -/
noncomputable def boydConcreteB {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  let y := boydRectActionCLM A x
  let σp := realLpPowerSum p y
  let DxInv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.diagonal (fun i => |x i| ^ (2 - p))).mulVecLin.toContinuousLinearMap
  let Dy : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    (Matrix.diagonal (fun i => |y i| ^ (p - 2))).mulVecLin.toContinuousLinearMap
  σp⁻¹ • (DxInv.comp
    (boydRectTransposeActionCLM A |>.comp
      (Dy.comp (boydRectActionCLM A))))

theorem boydConcreteB_apply {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (j : Fin n) :
    boydConcreteB p A x h j =
      (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        |x j| ^ (2 - p) *
          (∑ i : Fin m, A i j *
            (|boydRectActionCLM A x i| ^ (p - 2) *
              boydRectActionCLM A h i)) := by
  simp [boydConcreteB, boydRectActionCLM_apply,
    boydRectTransposeActionCLM_apply, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply]
  ring

/-- The bundled normalized operator is the source `B` scaled by the attained
power sum. -/
theorem boydConcreteB_eq_smul_lemma3B {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) :
    boydConcreteB p A x h = fun j =>
      (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydLemma3B p A x h j := by
  funext j
  rw [boydConcreteB_apply]
  unfold boydLemma3B
  rw [show (∑ i : Fin m, A i j *
      (|boydRectActionCLM A x i| ^ (p - 2) * boydRectActionCLM A h i)) =
      ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  ring

private theorem boyd_weight_exponents_cancel {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * |a| ^ (2 - p) = 1 := by
  rw [← Real.rpow_add (abs_pos.mpr ha)]
  convert Real.rpow_zero |a| using 1
  ring

/-- Square-root scaling changes Boyd's weighted pairing into the ordinary
Euclidean inner product. -/
theorem inner_boydWeightScale_eq_weightedPair {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    inner ℝ (boydWeightEuclideanEquiv p x hxcoord g)
        (boydWeightEuclideanEquiv p x hxcoord h) =
      boydWeightedPair p x g h := by
  rw [PiLp.inner_apply]
  unfold boydWeightedPair
  apply Finset.sum_congr rfl
  intro i _
  have hw : 0 ≤ |x i| ^ (p - 2) :=
    (Real.rpow_pos_of_pos (abs_pos.mpr (hxcoord i)) _).le
  simp only [boydWeightEuclideanEquiv_apply]
  rw [real_inner_eq_re_inner]
  change (Real.sqrt (|x i| ^ (p - 2)) * h i) *
      (Real.sqrt (|x i| ^ (p - 2)) * g i) =
        |x i| ^ (p - 2) * g i * h i
  rw [show (Real.sqrt (|x i| ^ (p - 2)) * h i) *
      (Real.sqrt (|x i| ^ (p - 2)) * g i) =
        (Real.sqrt (|x i| ^ (p - 2))) ^ 2 * g i * h i by ring,
    Real.sq_sqrt hw]

/-- The exact stationary (nonlinear singular-vector) equation used in Boyd's
Lemma 3, including normalization and positivity of the attained value. -/
def IsBoydConcreteStationary {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  realLpPowerSum p x = 1 ∧
    0 < realLpPowerSum p (boydRectActionCLM A x) ∧
      ∀ j : Fin n,
        (∑ i : Fin m, A i j *
          (|boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A x i)) =
          realLpPowerSum p (boydRectActionCLM A x) *
            (|x j| ^ (p - 2) * x j)

/-- The stationary equation is exactly the source eigen-equation
`B x = S x`. -/
theorem boydLemma3B_apply_self_of_stationary {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hstat : IsBoydConcreteStationary p A x) :
    boydLemma3B p A x x = fun j =>
      realLpPowerSum p (boydRectActionCLM A x) * x j := by
  obtain ⟨_hunit, _hS, hraw⟩ := hstat
  funext j
  unfold boydLemma3B
  rw [show (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
      boydRectActionCLM A x i) =
      ∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i) by
    apply Finset.sum_congr rfl
    intro i _
    ring,
    hraw j]
  rw [show |x j| ^ (2 - p) *
      (realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * |x j| ^ (2 - p)) * x j by ring,
    boyd_weight_mul_inverse_weight (hxcoord j), mul_one]

/-- The normalized concrete operator fixes the stationary radial vector. -/
theorem boydConcreteB_apply_self_of_stationary {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hstat : IsBoydConcreteStationary p A x) :
    boydConcreteB p A x x = x := by
  have hstat' := hstat
  obtain ⟨_hunit, hS, _hraw⟩ := hstat
  rw [boydConcreteB_eq_smul_lemma3B,
    boydLemma3B_apply_self_of_stationary p A x hxcoord hstat']
  funext j
  have hSne : realLpPowerSum p (boydRectActionCLM A x) ≠ 0 := ne_of_gt hS
  simp [hSne]

/-- The central algebraic identity in Boyd Lemma 3.  It proves weighted
self-adjointness and positive semidefiniteness without any stability premise. -/
theorem boydConcreteB_weightedPair {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    boydWeightedPair p x (boydConcreteB p A x g) h =
      (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        ∑ i : Fin m, |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A g i * boydRectActionCLM A h i := by
  rw [boydConcreteB_eq_smul_lemma3B, boydWeightedPair_smul_left,
    boydWeightedPair_lemma3B p A x g h hxcoord]

/-- Weighted self-adjointness of the concrete Boyd operator. -/
theorem boydConcreteB_weighted_symmetric {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    boydWeightedPair p x (boydConcreteB p A x g) h =
      boydWeightedPair p x g (boydConcreteB p A x h) := by
  rw [boydConcreteB_weightedPair p A x g h hxcoord]
  rw [show boydWeightedPair p x g (boydConcreteB p A x h) =
      boydWeightedPair p x (boydConcreteB p A x h) g by
    unfold boydWeightedPair
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [boydConcreteB_weightedPair p A x h g hxcoord]
  apply congrArg (fun t : ℝ =>
    (realLpPowerSum p (boydRectActionCLM A x))⁻¹ * t)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Weighted positive semidefiniteness of the concrete Boyd operator. -/
theorem boydConcreteB_weighted_nonneg {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x)) :
    0 ≤ boydWeightedPair p x (boydConcreteB p A x h) h := by
  rw [boydConcreteB_weightedPair p A x h h hxcoord]
  exact mul_nonneg (inv_nonneg.mpr hS.le) (Finset.sum_nonneg fun i _ => by
    have hw : 0 ≤ |boydRectActionCLM A x i| ^ (p - 2) :=
      Real.rpow_nonneg (abs_nonneg _) _
    nlinarith [sq_nonneg (boydRectActionCLM A h i)])

/-! ## The weighted tangent projection and the full stationary derivative -/

/-- The weighted radial coordinate `h ↦ [x,h]_x`, bundled continuously. -/
noncomputable def boydWeightedFunctional {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun h => boydWeightedPair p x x h
     map_add' := by
       intro g h
       unfold boydWeightedPair
       rw [← Finset.sum_add_distrib]
       apply Finset.sum_congr rfl
       intro i _
       simp only [Pi.add_apply]
       ring
     map_smul' := by
       intro c h
       unfold boydWeightedPair
       simp only [Pi.smul_apply, smul_eq_mul]
       rw [Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro i _
       simp only [RingHom.id_apply]
       ring } : (Fin n → ℝ) →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem boydWeightedFunctional_apply {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) :
    boydWeightedFunctional p x h = boydWeightedPair p x x h :=
  rfl

/-- Weighted-orthogonal projection onto the tangent hyperplane. -/
noncomputable def boydTangentProjection {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.id ℝ (Fin n → ℝ) -
    (boydWeightedFunctional p x).smulRight x

@[simp] theorem boydTangentProjection_apply {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) :
    boydTangentProjection p x h =
      fun i => h i - boydWeightedPair p x x h * x i := by
  rfl

/-- At a normalized point, the projection has tangent range. -/
theorem boydTangentProjection_is_tangent {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x x (boydTangentProjection p x h) = 0 := by
  rw [boydTangentProjection_apply,
    boydWeightedPair_sub_right,
    boydWeightedPair_x_self_eq_powerSum p x hxcoord, hunit]
  ring

/-- The projection fixes every tangent vector. -/
theorem boydTangentProjection_eq_self_of_tangent {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hh : boydWeightedPair p x x h = 0) :
    boydTangentProjection p x h = h := by
  funext i
  simp [boydTangentProjection_apply, hh]

/-- The projection is self-adjoint for Boyd's weighted pairing. -/
theorem boydTangentProjection_weighted_symmetric {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) :
    boydWeightedPair p x (boydTangentProjection p x g) h =
      boydWeightedPair p x g (boydTangentProjection p x h) := by
  rw [boydTangentProjection_apply, boydTangentProjection_apply,
    boydWeightedPair_sub_left, boydWeightedPair_sub_right]
  rw [boydWeightedPair_symm p x x h, boydWeightedPair_symm p x g x]
  ring

/-- Pythagoras for the weighted tangent projection. -/
theorem boydTangentProjection_pair_self {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x (boydTangentProjection p x h)
        (boydTangentProjection p x h) =
      boydWeightedPair p x h h - (boydWeightedPair p x x h) ^ 2 := by
  have hPt : boydWeightedPair p x x (boydTangentProjection p x h) = 0 :=
    boydTangentProjection_is_tangent p x h hxcoord hunit
  have hPP : boydTangentProjection p x (boydTangentProjection p x h) =
      boydTangentProjection p x h :=
    boydTangentProjection_eq_self_of_tangent p x _ hPt
  calc
    boydWeightedPair p x (boydTangentProjection p x h)
        (boydTangentProjection p x h) =
        boydWeightedPair p x h
          (boydTangentProjection p x (boydTangentProjection p x h)) :=
      boydTangentProjection_weighted_symmetric p x h
        (boydTangentProjection p x h)
    _ = boydWeightedPair p x h (boydTangentProjection p x h) := by rw [hPP]
    _ = boydWeightedPair p x h h -
        boydWeightedPair p x x h * boydWeightedPair p x h x := by
      rw [boydTangentProjection_apply, boydWeightedPair_sub_right]
    _ = boydWeightedPair p x h h - (boydWeightedPair p x x h) ^ 2 := by
      rw [boydWeightedPair_symm p x h x]
      ring

/-- The full stationary linearization, written as the source-honest
weighted-orthogonal sandwich `P B P`. -/
noncomputable def boydConcreteFullDerivative {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (boydTangentProjection p x).comp
    ((boydConcreteB p A x).comp (boydTangentProjection p x))

theorem boydConcreteFullDerivative_apply {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) :
    boydConcreteFullDerivative p A x h =
      boydTangentProjection p x
        (boydConcreteB p A x (boydTangentProjection p x h)) :=
  rfl

/-- At a stationary point `P B = P B P`; hence the full sandwich is the
normalized projected source operator. -/
theorem boydConcreteFullDerivative_eq_normalized_projected
    {m n : ℕ} (p : ℝ) (A : Fin m → Fin n → ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ j, x j ≠ 0)
    (hstat : IsBoydConcreteStationary p A x) :
    boydConcreteFullDerivative p A x h = fun j =>
      (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  have hstat' := hstat
  obtain ⟨hunit, _hS, _hraw⟩ := hstat
  let S := realLpPowerSum p (boydRectActionCLM A x)
  have hBx : boydLemma3B p A x x = fun j => S * x j := by
    simpa [S] using boydLemma3B_apply_self_of_stationary
      p A x hxcoord hstat'
  have hproj := boydProjectedLemma3B_eq_projection
    p S A x h hxcoord hunit hBx
  calc
    boydConcreteFullDerivative p A x h =
        boydTangentProjection p x
          (boydConcreteB p A x (boydTangentProjection p x h)) := rfl
    _ = boydTangentProjection p x
          (S⁻¹ • boydLemma3B p A x (boydTangentProjection p x h)) := by
      rw [boydConcreteB_eq_smul_lemma3B]
      rfl
    _ = S⁻¹ • boydTangentProjection p x
          (boydLemma3B p A x (boydTangentProjection p x h)) := by
      rw [map_smul]
    _ = S⁻¹ • boydProjectedLemma3B p A x
          (boydTangentProjection p x h) := by rfl
    _ = S⁻¹ • boydProjectedLemma3B p A x h := by
      rw [show boydTangentProjection p x h = boydWeightedProjection p x h by rfl,
        hproj]
    _ = fun j => S⁻¹ * boydProjectedLemma3B p A x h j := by rfl

/-- The full sandwich has tangent range. -/
theorem boydConcreteFullDerivative_is_tangent {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x x (boydConcreteFullDerivative p A x h) = 0 := by
  rw [boydConcreteFullDerivative_apply]
  exact boydTangentProjection_is_tangent p x _ hxcoord hunit

/-- The full sandwich kills the radial direction. -/
theorem boydConcreteFullDerivative_apply_self {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydConcreteFullDerivative p A x x = 0 := by
  have hpair : boydWeightedPair p x x x = 1 := by
    rw [boydWeightedPair_x_self_eq_powerSum p x hxcoord, hunit]
  have hPx : boydTangentProjection p x x = 0 := by
    funext i
    simp [boydTangentProjection_apply, hpair]
  rw [boydConcreteFullDerivative_apply, hPx, map_zero, map_zero]

/-- Weighted self-adjointness of the full sandwich. -/
theorem boydConcreteFullDerivative_weighted_symmetric {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    boydWeightedPair p x (boydConcreteFullDerivative p A x g) h =
      boydWeightedPair p x g (boydConcreteFullDerivative p A x h) := by
  rw [boydConcreteFullDerivative_apply, boydConcreteFullDerivative_apply]
  rw [boydTangentProjection_weighted_symmetric]
  rw [boydConcreteB_weighted_symmetric p A x
    (boydTangentProjection p x g) (boydTangentProjection p x h) hxcoord]
  rw [← boydTangentProjection_weighted_symmetric]

/-- Weighted positive semidefiniteness of the full sandwich. -/
theorem boydConcreteFullDerivative_weighted_nonneg {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x)) :
    0 ≤ boydWeightedPair p x (boydConcreteFullDerivative p A x h) h := by
  rw [boydConcreteFullDerivative_apply,
    boydTangentProjection_weighted_symmetric]
  exact boydConcreteB_weighted_nonneg A x (boydTangentProjection p x h)
    hxcoord hS

/-- The Rayleigh form of `P B P` is the `B` Rayleigh form of the projected
direction. -/
theorem boydConcreteFullDerivative_pair_eq_B_projection {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) :
    boydWeightedPair p x (boydConcreteFullDerivative p A x h) h =
      boydWeightedPair p x
        (boydConcreteB p A x (boydTangentProjection p x h))
        (boydTangentProjection p x h) := by
  rw [boydConcreteFullDerivative_apply,
    boydTangentProjection_weighted_symmetric]

/-! ## Genuine constrained second variation -/

/-- The Lagrangian line through `x` in direction `h` for the constrained
power objective. -/
noncomputable def boydConstrainedLagrangianLine {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i : Fin m,
      |boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ p) -
    realLpPowerSum p (boydRectActionCLM A x) *
      ∑ j : Fin n, |x j + t * h j| ^ p

/-- The literal first-derivative formula of the constrained Lagrangian line. -/
noncomputable def boydConstrainedLagrangianFirst {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i : Fin m, p * boydRectActionCLM A h i *
      (|boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ (p - 2) *
        (boydRectActionCLM A x i + t * boydRectActionCLM A h i))) -
    realLpPowerSum p (boydRectActionCLM A x) *
      ∑ j : Fin n, p * h j *
        (|x j + t * h j| ^ (p - 2) * (x j + t * h j))

/-- The quadratic second variation of
`powerSum p (A u) - powerSum p (A x) * powerSum p u` at `x`.
The theorem below identifies it with an actual second derivative, so this is
not a renamed contraction premise. -/
noncomputable def boydConstrainedSecondVariation {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) : ℝ :=
  p * (p - 1) *
    ((∑ i : Fin m, |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i * boydRectActionCLM A h i) -
      realLpPowerSum p (boydRectActionCLM A x) *
        boydWeightedPair p x h h)

private theorem hasDerivAt_abs_rpow_affine {p a b : ℝ} (hp : 1 < p) :
    HasDerivAt (fun t : ℝ => |a + t * b| ^ p)
      (p * |a| ^ (p - 2) * a * b) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hbase : HasDerivAt (fun u : ℝ => |u| ^ p)
      (p * |a| ^ (p - 2) * a) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow a hp
  convert hbase.comp 0 hline using 1 <;>
    simp only [zero_mul, add_zero, Function.comp_apply] <;> ring

/-- The displayed first formula is the actual derivative of the constrained
Lagrangian line. -/
theorem boydConstrainedLagrangianLine_hasDerivAt
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) :
    HasDerivAt (boydConstrainedLagrangianLine p A x h)
      (boydConstrainedLagrangianFirst p A x h 0) 0 := by
  have hN : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        |boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ p)
      (∑ i : Fin m, p * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A x i * boydRectActionCLM A h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_abs_rpow_affine hp
  have hD : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n, |x j + t * h j| ^ p)
      (∑ j : Fin n, p * |x j| ^ (p - 2) * x j * h j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact hasDerivAt_abs_rpow_affine hp
  have htot := hN.sub (hD.const_mul
    (realLpPowerSum p (boydRectActionCLM A x)))
  convert htot using 1
  unfold boydConstrainedLagrangianFirst
  simp only [zero_mul, add_zero]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem hasDerivAt_gradientFactor_affine {p a b : ℝ}
    (ha : a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => b * (|a + t * b| ^ (p - 2) * (a + t * b)))
      (b * ((p - 1) * |a| ^ (p - 2) * b)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfactor : HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u)
      ((p - 1) * |a| ^ (p - 2)) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self p a ha
  have hbase := hfactor.comp 0 hline
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hbase.const_mul b

/-- The second-variation quadratic is the actual derivative of the literal
first-derivative formula.  Together with the preceding theorem this is a
genuine second derivative witness, not a contraction hypothesis. -/
theorem boydConstrainedLagrangianFirst_hasDerivAt
    {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0) :
    HasDerivAt (boydConstrainedLagrangianFirst p A x h)
      (boydConstrainedSecondVariation p A x h) 0 := by
  have hN : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, p *
        boydRectActionCLM A h i *
          (|boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ (p - 2) *
            (boydRectActionCLM A x i + t * boydRectActionCLM A h i)))
      (∑ i : Fin m, p * (p - 1) *
        |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i * boydRectActionCLM A h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi := (hasDerivAt_gradientFactor_affine
      (p := p) (a := boydRectActionCLM A x i)
      (b := boydRectActionCLM A h i) (hycoord i)).const_mul p
    convert hi using 1 <;> ring_nf
  have hD : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n, p *
        h j * (|x j + t * h j| ^ (p - 2) * (x j + t * h j)))
      (∑ j : Fin n, p * (p - 1) * |x j| ^ (p - 2) * h j * h j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    have hj := (hasDerivAt_gradientFactor_affine
      (p := p) (a := x j) (b := h j) (hxcoord j)).const_mul p
    convert hj using 1 <;> ring_nf
  have htot := hN.sub (hD.const_mul
    (realLpPowerSum p (boydRectActionCLM A x)))
  convert htot using 1
  unfold boydConstrainedSecondVariation boydWeightedPair
  have hout : (∑ i : Fin m, p * (p - 1) *
      |boydRectActionCLM A x i| ^ (p - 2) *
      boydRectActionCLM A h i * boydRectActionCLM A h i) =
      p * (p - 1) * ∑ i : Fin m,
        |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i * boydRectActionCLM A h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hin : (∑ j : Fin n, p * (p - 1) * |x j| ^ (p - 2) * h j * h j) =
      p * (p - 1) * ∑ j : Fin n, |x j| ^ (p - 2) * h j * h j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hout, hin]
  ring

/-- Source-facing certificate that the constrained second variation is an
actual second derivative. -/
theorem boydConstrainedSecondVariation_is_second_derivative
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0) :
    HasDerivAt (boydConstrainedLagrangianLine p A x h)
        (boydConstrainedLagrangianFirst p A x h 0) 0 ∧
      HasDerivAt (boydConstrainedLagrangianFirst p A x h)
        (boydConstrainedSecondVariation p A x h) 0 :=
  ⟨boydConstrainedLagrangianLine_hasDerivAt hp A x h,
    boydConstrainedLagrangianFirst_hasDerivAt A x h hxcoord hycoord⟩

/-- Exact Hessian/Rayleigh identity for the concrete normalized Gram
operator. -/
theorem boydConstrainedSecondVariation_eq_B_rayleigh {m n : ℕ}
    (p : ℝ) (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x)) :
    boydConstrainedSecondVariation p A x h =
      p * (p - 1) * realLpPowerSum p (boydRectActionCLM A x) *
        (boydWeightedPair p x (boydConcreteB p A x h) h -
          boydWeightedPair p x h h) := by
  rw [boydConcreteB_weightedPair p A x h h hxcoord]
  unfold boydConstrainedSecondVariation
  have hSne : realLpPowerSum p (boydRectActionCLM A x) ≠ 0 := ne_of_gt hS
  field_simp

/-- On tangent vectors the second variation is the Rayleigh defect of the
full `P B P` derivative. -/
theorem boydConstrainedSecondVariation_eq_full_rayleigh_of_tangent
    {m n : ℕ} (p : ℝ) (A : Fin m → Fin n → ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hh : boydWeightedPair p x x h = 0) :
    boydConstrainedSecondVariation p A x h =
      p * (p - 1) * realLpPowerSum p (boydRectActionCLM A x) *
        (boydWeightedPair p x (boydConcreteFullDerivative p A x h) h -
          boydWeightedPair p x h h) := by
  rw [boydConstrainedSecondVariation_eq_B_rayleigh p A x h hxcoord hS]
  have hPh : boydTangentProjection p x h = h :=
    boydTangentProjection_eq_self_of_tangent p x h hh
  have hpair : boydWeightedPair p x
      (boydConcreteFullDerivative p A x h) h =
      boydWeightedPair p x (boydConcreteB p A x h) h := by
    rw [boydConcreteFullDerivative_apply, hPh,
      boydTangentProjection_weighted_symmetric, hPh]
  rw [hpair]

/-- Nondegeneracy is a uniform negative gap in the actual constrained second
variation, only on tangent directions. -/
def IsBoydConcreteNondegenerate {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ h : Fin n → ℝ,
    boydWeightedPair p x x h = 0 →
      boydConstrainedSecondVariation p A x h ≤
        -η * boydWeightedPair p x h h

/-- The corrected, audit-facing meaning of Boyd's “strong local maximum”:
an actual normalized stationary point together with a uniform negative gap
for its constrained second variation.  This is deliberately stronger than
an ordinary `StrictMaximum`, which need not have a nondegenerate Hessian. -/
def IsBoydConcreteStrongLocalMaximum {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  IsBoydConcreteStationary p A x ∧
    IsBoydConcreteNondegenerate p A x

/-- Positivity of Boyd's weighted square. -/
theorem boydWeightedPair_self_nonneg {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) : 0 ≤ boydWeightedPair p x h h := by
  unfold boydWeightedPair
  exact Finset.sum_nonneg fun i _ => by
    have hw : 0 ≤ |x i| ^ (p - 2) := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith [sq_nonneg (h i)]

/-- Projection cannot increase the weighted square. -/
theorem boydTangentProjection_pair_le {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x (boydTangentProjection p x h)
        (boydTangentProjection p x h) ≤
      boydWeightedPair p x h h := by
  rw [boydTangentProjection_pair_self p x h hxcoord hunit]
  exact sub_le_self _ (sq_nonneg _)

/-- A negative constrained second-variation gap gives a strict weighted
Rayleigh gap for the full derivative, including the radial direction. -/
theorem boydConcreteFullDerivative_weighted_rayleigh_gap
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ h : Fin n → ℝ,
      boydWeightedPair p x (boydConcreteFullDerivative p A x h) h ≤
        (1 - δ) * boydWeightedPair p x h h := by
  obtain ⟨η, hη, hgap⟩ := hnondeg
  let κ : ℝ := p * (p - 1) *
    realLpPowerSum p (boydRectActionCLM A x)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact mul_pos (mul_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hp)) hS
  let δ : ℝ := min (η / κ) (1 / 2)
  have hδ0 : 0 < δ := lt_min (div_pos hη hκ) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hκδ : κ * δ ≤ η := by
    have hd : δ ≤ η / κ := min_le_left _ _
    calc
      κ * δ ≤ κ * (η / κ) :=
        mul_le_mul_of_nonneg_left hd hκ.le
      _ = η := by field_simp
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro h
  let t := boydTangentProjection p x h
  have ht : boydWeightedPair p x x t = 0 :=
    boydTangentProjection_is_tangent p x h hxcoord hunit
  have hWt : 0 ≤ boydWeightedPair p x t t :=
    boydWeightedPair_self_nonneg p x t
  have hH := hgap t ht
  have hHid := boydConstrainedSecondVariation_eq_B_rayleigh
    p A x t hxcoord hS
  have hHδ : boydConstrainedSecondVariation p A x t ≤
      -(κ * δ) * boydWeightedPair p x t t := by
    calc
      boydConstrainedSecondVariation p A x t ≤
          -η * boydWeightedPair p x t t := hH
      _ ≤ -(κ * δ) * boydWeightedPair p x t t := by
        have hm := mul_le_mul_of_nonneg_right hκδ hWt
        nlinarith
  have hBt : boydWeightedPair p x (boydConcreteB p A x t) t ≤
      (1 - δ) * boydWeightedPair p x t t := by
    rw [hHid] at hHδ
    change κ *
        (boydWeightedPair p x (boydConcreteB p A x t) t -
          boydWeightedPair p x t t) ≤
        -(κ * δ) * boydWeightedPair p x t t at hHδ
    nlinarith
  have ht_le := boydTangentProjection_pair_le p x h hxcoord hunit
  rw [boydConcreteFullDerivative_pair_eq_B_projection]
  change boydWeightedPair p x (boydConcreteB p A x t) t ≤ _
  calc
    boydWeightedPair p x (boydConcreteB p A x t) t ≤
        (1 - δ) * boydWeightedPair p x t t := hBt
    _ ≤ (1 - δ) * boydWeightedPair p x h h :=
      mul_le_mul_of_nonneg_left ht_le (sub_nonneg.mpr hδ1.le)

/-! ## Euclidean transport and whole-space stable power -/

/-- The full derivative conjugated into the Euclidean weighted coordinates. -/
noncomputable def boydEuclideanFullDerivative {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (boydWeightEuclideanEquiv p x hxcoord).toContinuousLinearMap.comp
    ((boydConcreteFullDerivative p A x).comp
      (boydWeightEuclideanEquiv p x hxcoord).symm.toContinuousLinearMap)

/-- Euclidean inner products of the conjugate are exactly weighted pairings
of the original full derivative. -/
theorem inner_boydEuclideanFullDerivative {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (g h : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (boydEuclideanFullDerivative p A x hxcoord g) h =
      boydWeightedPair p x
        (boydConcreteFullDerivative p A x
          ((boydWeightEuclideanEquiv p x hxcoord).symm g))
        ((boydWeightEuclideanEquiv p x hxcoord).symm h) := by
  let e := boydWeightEuclideanEquiv p x hxcoord
  have hv := inner_boydWeightScale_eq_weightedPair p x
    (boydConcreteFullDerivative p A x (e.symm g)) (e.symm h) hxcoord
  simpa [e, boydEuclideanFullDerivative] using hv

/-- The Euclidean conjugate is genuinely symmetric. -/
theorem boydEuclideanFullDerivative_symmetric {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    (boydEuclideanFullDerivative p A x hxcoord :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
  intro g h
  change inner ℝ (boydEuclideanFullDerivative p A x hxcoord g) h =
    inner ℝ g (boydEuclideanFullDerivative p A x hxcoord h)
  rw [inner_boydEuclideanFullDerivative]
  rw [← real_inner_comm g
    (boydEuclideanFullDerivative p A x hxcoord h)]
  rw [inner_boydEuclideanFullDerivative]
  rw [boydConcreteFullDerivative_weighted_symmetric p A x _ _ hxcoord]
  exact boydWeightedPair_symm p x _ _

/-- The Euclidean conjugate is genuinely positive semidefinite. -/
theorem boydEuclideanFullDerivative_psd {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (h : EuclideanSpace ℝ (Fin n)) :
    0 ≤ inner ℝ (boydEuclideanFullDerivative p A x hxcoord h) h := by
  rw [inner_boydEuclideanFullDerivative]
  exact boydConcreteFullDerivative_weighted_nonneg A x _ hxcoord hS

/-- The constrained Hessian gap becomes an ordinary Euclidean Rayleigh gap
after diagonal scaling. -/
theorem boydEuclideanFullDerivative_rayleigh_gap
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ h : EuclideanSpace ℝ (Fin n),
        inner ℝ (boydEuclideanFullDerivative p A x hxcoord h) h ≤
          (1 - δ) * ‖h‖ ^ 2 := by
  obtain ⟨δ, hδ0, hδ1, hgap⟩ :=
    boydConcreteFullDerivative_weighted_rayleigh_gap
      hp A x hxcoord hunit hS hnondeg
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro h
  let e := boydWeightEuclideanEquiv p x hxcoord
  let g : Fin n → ℝ := e.symm h
  have hnorm : boydWeightedPair p x g g = ‖h‖ ^ 2 := by
    have hs := inner_boydWeightScale_eq_weightedPair p x g g hxcoord
    rw [show boydWeightEuclideanEquiv p x hxcoord g = h by
      exact e.apply_symm_apply h] at hs
    rw [real_inner_self_eq_norm_sq] at hs
    exact hs.symm
  have hg := hgap g
  rw [inner_boydEuclideanFullDerivative]
  simpa [g, hnorm] using hg

/-- Concrete nondegeneracy gives a strict contraction of the full derivative
in Boyd's weighted Euclidean coordinates. -/
theorem boydEuclideanFullDerivative_strict_contraction
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ c : NNReal, 0 < c ∧ c < 1 ∧
      ‖boydEuclideanFullDerivative p A x hxcoord‖ ≤ (c : ℝ) := by
  obtain ⟨δ, hδ0, hδ1, hupper⟩ :=
    boydEuclideanFullDerivative_rayleigh_gap
      hp A x hxcoord hunit hS hnondeg
  have hnorm := opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap
    (boydEuclideanFullDerivative p A x hxcoord) hδ1
    (boydEuclideanFullDerivative_symmetric p A x hxcoord)
    (boydEuclideanFullDerivative_psd A x hxcoord hS) hupper
  let c : NNReal := ⟨1 - δ, (sub_pos.mpr hδ1).le⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · change 0 < (1 - δ : ℝ)
    exact sub_pos.mpr hδ1
  · change (1 - δ : ℝ) < 1
    linarith
  · simpa [c] using hnorm

/-- Whole-space stable power of the full concrete derivative in the
repository's original norm.  This includes the radial direction, which the
derivative kills, and therefore feeds the existing local convergence theorem
without a hidden tangent-only premise. -/
theorem boydConcreteFullDerivative_power_stable
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hS : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ N : ℕ, 0 < N ∧ ∃ K : NNReal, 0 < K ∧ K < 1 ∧
      ‖(boydConcreteFullDerivative p A x) ^ N‖ ≤ (K : ℝ) ^ N := by
  obtain ⟨c, hc0, hc1, hc⟩ :=
    boydEuclideanFullDerivative_strict_contraction
      hp A x hxcoord hunit hS hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  have hK0 : 0 < K := lt_of_lt_of_le hc0 (le_of_lt hcK)
  let e := (boydWeightEuclideanEquiv p x hxcoord).symm
  obtain ⟨N, hN, hpow⟩ :=
    exists_pos_power_bound_of_equivalent_contraction
      e (boydConcreteFullDerivative p A x) hcK (by
        simpa [e, boydEuclideanFullDerivative] using hc)
  exact ⟨N, hN, K, hK0, hK1, hpow⟩

/-! ## Actual update and source-facing local convergence -/

/-- Starting the literal Algorithm 15.1 trace at its `r`th iterate is the
tail of the original trace. -/
theorem rectPNormPair_xseq_shift_add {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (r k : ℕ) :
    P.xseq (P.xseq x0 r) k = P.xseq x0 (r + k) := by
  rw [rectPNormPair_xseq_eq_iterate, rectPNormPair_xseq_eq_iterate,
    rectPNormPair_xseq_eq_iterate]
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Convergence of one finite tail of the literal trace is convergence of the
full trace. -/
theorem tendsto_rectPNormPair_xseq_of_tail {m n : ℕ}
    (P : RectPNormPair m n) (x0 x : Fin n → ℝ) (r : ℕ)
    (h : Tendsto (P.xseq (P.xseq x0 r)) atTop (nhds x)) :
    Tendsto (P.xseq x0) atTop (nhds x) := by
  have htail : Tendsto (fun k => P.xseq x0 (k + r)) atTop (nhds x) := by
    convert h using 1
    funext k
    rw [rectPNormPair_xseq_shift_add, Nat.add_comm]
  exact (tendsto_add_atTop_iff_nat r).mp htail

/-- A convergent sampled trace eventually enters every positive ball for the
finite-power adapted norm.  The proof uses its explicit upper comparison
with the ambient norm, so no unproved continuity of an abstract seminorm is
being used. -/
theorem exists_subsequence_in_powerAdapted_ball
    {m n : ℕ} (P : RectPNormPair m n) (x0 x : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (c : NNReal) (N : ℕ) (φ : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hcluster : Tendsto (fun r => P.xseq x0 (φ r)) atTop (nhds x)) :
    ∃ r : ℕ,
      powerAdaptedSeminorm L c N (P.xseq x0 (φ r) - x) ≤ δ := by
  let B := powerAdaptedBound L c N
  have hB : 0 ≤ B := by
    unfold B powerAdaptedBound
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
  have hBp : 0 < B + 1 := by linarith
  let ε : ℝ := δ / (B + 1)
  have hε : 0 < ε := div_pos hδ hBp
  obtain ⟨r0, hr0⟩ := (Metric.tendsto_atTop.1 hcluster) ε hε
  have hdist := hr0 r0 le_rfl
  rw [dist_eq_norm] at hdist
  refine ⟨r0, ?_⟩
  apply le_of_lt
  calc
    powerAdaptedSeminorm L c N (P.xseq x0 (φ r0) - x) ≤
        B * ‖P.xseq x0 (φ r0) - x‖ :=
      powerAdaptedSeminorm_le_bound_mul_norm L c N _
    _ ≤ (B + 1) * ‖P.xseq x0 (φ r0) - x‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (B + 1) * ε := mul_lt_mul_of_pos_left hdist hBp
    _ = δ := by
      dsimp [ε]
      field_simp [ne_of_gt hBp]

/-- Uniform local-linear theorem for the literal rectangular Boyd update.
The fixed-point equation and the Fréchet derivative are derived from raw
stationarity; nondegenerate constrained curvature supplies the stable power.
The only additional regularity assumptions are precisely the nonzero
coordinates used by the current smooth-domain Lemma 2. -/
theorem rect_general_boyd_concrete_local_linear_uniform
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ x0 : Fin n → ℝ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              (x0 - x) ≤ δ →
            (∀ k : ℕ,
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  ((RectPNormPair.general hn hpq A).xseq x0 k - x) ≤
                (K : ℝ) ^ k *
                  powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                    (x0 - x)) ∧
            Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
              atTop (nhds x) := by
  have hstat' := hstat
  obtain ⟨hunit, hS, hstationary⟩ := hstat
  have hfixed := rect_general_xnext_eq_of_stationarity
    hm hn hpq A x hxcoord hycoord hunit hstationary
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hS hstationary
  have hderiv := rect_general_xnext_hasFDerivAt_boyd
    hm hn hpq A x hycoord hzcoord
  have hL : boydSmoothRectDerivative (p := p) (q := q) A x =
      boydConcreteFullDerivative p A x := by
    ext h j
    rw [boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
      hpq A x h hxcoord hycoord hunit hS hstationary]
    rw [boydConcreteFullDerivative_eq_normalized_projected
      p A x h hxcoord hstat']
  rw [hL] at hderiv
  obtain ⟨N, hN, c, hc0, hc1, hpow⟩ :=
    boydConcreteFullDerivative_power_stable
      hpq.lt A x hxcoord hunit hS hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_local_powerAdaptedSeminormContraction
      hN hc0 hcK hK1 hpow hfixed hderiv
  refine ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, ?_⟩
  intro x0 hx0
  have hgeom :=
    iterate_seminorm_le_geometric_of_localSeminormContraction hlocal hx0
  have hconv := tendsto_iterate_of_localSeminormContraction
    (fun y => norm_le_powerAdaptedSeminorm
      (boydConcreteFullDerivative p A x) c hN y) hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate]
    exact (hgeom k).1
  · rw [show (RectPNormPair.general hn hpq A).xseq x0 =
        (fun k : ℕ =>
          (RectPNormPair.general hn hpq A).xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate _ _ _]
    exact hconv

/-- Fixed-start specialization of the preceding uniform neighborhood
theorem. -/
theorem rect_general_boyd_concrete_local_linear
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
        (powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
            (x0 - x) ≤ δ →
          (∀ k : ℕ,
            powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 k - x) ≤
              (K : ℝ) ^ k *
                powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  (x0 - x)) ∧
          Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
            atTop (nhds x)) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal⟩ :=
    rect_general_boyd_concrete_local_linear_uniform
      hm hn hpq A x hxcoord hycoord hstat hnondeg
  exact ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal x0⟩

/-- Higham's source-facing implication: if the corrected nondegenerate
stationary point is a subsequential limit of the literal trace, then some
sampled entry point lies in the uniform adapted neighborhood.  The ensuing
tail has an explicit one-step geometric rate, and deleting the finite prefix
gives convergence of the full original trace.  No local-start assumption is
present. -/
theorem rect_general_boyd_concrete_linear_of_subsequential_limit
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x)
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hcluster : Tendsto
      (fun s => (RectPNormPair.general hn hpq A).xseq x0 (φ s))
      atTop (nhds x)) :
    ∃ r N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧
        (∀ k : ℕ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              ((RectPNormPair.general hn hpq A).xseq x0 (φ r + k) - x) ≤
            (K : ℝ) ^ k *
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 (φ r) - x)) ∧
        Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
          atTop (nhds x) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal⟩ :=
    rect_general_boyd_concrete_local_linear_uniform
      hm hn hpq A x hxcoord hycoord hstat hnondeg
  obtain ⟨r, hr⟩ := exists_subsequence_in_powerAdapted_ball
    (RectPNormPair.general hn hpq A) x0 x
    (boydConcreteFullDerivative p A x) c N φ hδ hcluster
  obtain ⟨hgeomTail, hconvTail⟩ :=
    hlocal ((RectPNormPair.general hn hpq A).xseq x0 (φ r)) hr
  refine ⟨r, N, hN, c, K, hc0, hcK, hK1, ?_, ?_⟩
  · intro k
    simpa only [rectPNormPair_xseq_shift_add] using hgeomTail k
  · exact tendsto_rectPNormPair_xseq_of_tail
      (RectPNormPair.general hn hpq A) x0 x (φ r) hconvTail

/-- Source-facing wrapper of the preceding theorem under the corrected
single hypothesis called a “strong local maximum”.  The definition records
the nondegeneracy missing from an arbitrary strict maximum; it does not
silently repair the mismatch in Boyd's printed wording. -/
theorem higham15_boyd_concrete_linear_of_strongLocalMaximum_subsequentialLimit
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstrong : IsBoydConcreteStrongLocalMaximum p A x)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hcluster : Tendsto
      (fun s => (RectPNormPair.general hn hpq A).xseq x0 (φ s))
      atTop (nhds x)) :
    ∃ r N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧
        (∀ k : ℕ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              ((RectPNormPair.general hn hpq A).xseq x0 (φ r + k) - x) ≤
            (K : ℝ) ^ k *
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 (φ r) - x)) ∧
        Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
          atTop (nhds x) :=
  rect_general_boyd_concrete_linear_of_subsequential_limit
    hm hn hpq A x0 x hxcoord hycoord hstrong.1 hstrong.2 φ hφ hcluster

end NumStability.Ch15
