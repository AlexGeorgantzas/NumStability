/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 14, Problem 14.2 and equation (14.14).

This module gives the Method 2B part of the Problem 14.2 analysis under the
abstract Chapter 13 matrix-product and triangular-solve assumptions.  The two
products in the off-diagonal update are represented independently by
`MatMulFirstOrderSpec`; no conventional multiplication implementation is
chosen.  A right-oriented (13.5) specification supplies the leading diagonal
block relation `X11 * L11 = I + Delta11`.

The resulting left-residual estimate retains the factor
`norm(X11) * norm(L11)`.  Thus the operation assumptions derive Higham's
obstruction faithfully, but do not imply the stable Method 1B/Method 2C bound.
No final residual inequality or normalized counterexample is assumed.
-/

import NumStability.Algorithms.Ch14Problem142
import NumStability.Algorithms.MatrixInversionMethod2BInstance

namespace NumStability.Ch14Ext

/-! ### First-order transport through an exact matrix product -/

/-- A first-order error matrix remains first order after postmultiplication.
The dimension factor is explicit because `maxEntryNormRect` is the entrywise
maximum norm. -/
theorem higham14_problem14_2_firstOrder_mul_right {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (u leading : ℝ) (E : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ)
    (hE : FirstOrderLe u leading (maxEntryNormRect hm hn E)) :
    FirstOrderLe u
      (leading * ((n : ℝ) * maxEntryNormRect hn hp B))
      (maxEntryNormRect hm hp (E * B)) := by
  apply FirstOrderLe.bound_mul_nonneg_right hE
  · exact mul_nonneg (Nat.cast_nonneg n) (maxEntryNormRect_nonneg hn hp B)
  · calc
      maxEntryNormRect hm hp (E * B)
          ≤ (n : ℝ) * maxEntryNormRect hm hn E *
              maxEntryNormRect hn hp B := by
            simpa [rectMatMul, Matrix.mul_apply] using
              maxEntryNormRect_rectMatMul_le hm hn hp E B
      _ = maxEntryNormRect hm hn E *
          ((n : ℝ) * maxEntryNormRect hn hp B) := by ring

/-- A first-order error matrix remains first order after premultiplication. -/
theorem higham14_problem14_2_firstOrder_mul_left {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (u leading : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (E : Matrix (Fin n) (Fin p) ℝ)
    (hE : FirstOrderLe u leading (maxEntryNormRect hn hp E)) :
    FirstOrderLe u
      (leading * ((n : ℝ) * maxEntryNormRect hm hn A))
      (maxEntryNormRect hm hp (A * E)) := by
  apply FirstOrderLe.bound_mul_nonneg_right hE
  · exact mul_nonneg (Nat.cast_nonneg n) (maxEntryNormRect_nonneg hm hn A)
  · calc
      maxEntryNormRect hm hp (A * E)
          ≤ (n : ℝ) * maxEntryNormRect hm hn A *
              maxEntryNormRect hn hp E := by
            simpa [rectMatMul, Matrix.mul_apply] using
              maxEntryNormRect_rectMatMul_le hm hn hp A E
      _ = maxEntryNormRect hn hp E *
          ((n : ℝ) * maxEntryNormRect hm hn A) := by ring

/-! ### Two-product Method 2B update -/

/-- Operation-level Method 2B update at an arbitrary block split.

`That` is the first computed product `fl(X22 * L21)`, `Phat` is the second
computed product `fl(That * X11)`, and the computed off-diagonal block is
`X21 = -Phat`.  Both products satisfy arbitrary instances of (13.4). -/
structure Higham14Problem142Method2BStepSpec {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u cFirst cSecond : ℝ)
    (X22 : Matrix (Fin m) (Fin m) ℝ)
    (L21 : Matrix (Fin m) (Fin r) ℝ)
    (X11 : Matrix (Fin r) (Fin r) ℝ)
    (That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ) : Prop where
  first_product : MatMulFirstOrderSpec u cFirst
    (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
    (maxEntryNormRect hm hr DeltaFirst)
    X22 L21 That DeltaFirst
  second_product : MatMulFirstOrderSpec u cSecond
    (maxEntryNormRect hm hr That) (maxEntryNormRect hr hr X11)
    (maxEntryNormRect hm hr DeltaSecond)
    That X11 Phat DeltaSecond
  update : X21 = -Phat

/-- The perturbation produced by the two abstract products. -/
noncomputable def higham14_problem14_2_method2B_updateDelta {r m : ℕ}
    (DeltaFirst : Matrix (Fin m) (Fin r) ℝ)
    (X11 : Matrix (Fin r) (Fin r) ℝ)
    (DeltaSecond : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin m) (Fin r) ℝ :=
  -(DeltaFirst * X11 + DeltaSecond)

/-- The two (13.4) equations derive equation (14.14); the update equation is
not an additional residual hypothesis. -/
theorem Higham14Problem142Method2BStepSpec.update_equation {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond : ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond) :
    X21 = -(X22 * L21 * X11) +
      higham14_problem14_2_method2B_updateDelta DeltaFirst X11 DeltaSecond := by
  rw [h.update, h.second_product.equation, h.first_product.equation]
  simp only [higham14_problem14_2_method2B_updateDelta]
  rw [Matrix.add_mul]
  abel

/-- The operation-derived perturbation is exactly the perturbation named by
the existing equation-(14.14) Method 2B surface. -/
theorem Higham14Problem142Method2BStepSpec.existing_updateDelta_eq {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond : ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond) :
    higham14_method2BBlockUpdateDelta X21 X22 L21 X11 =
      higham14_problem14_2_method2B_updateDelta DeltaFirst X11 DeltaSecond := by
  rw [h.update_equation]
  ext i j
  simp only [higham14_method2BBlockUpdateDelta,
    higham14_method2BBlockUpdateExact,
    higham14_problem14_2_method2B_updateDelta,
    Matrix.add_apply, Matrix.neg_apply]
  change
    (-(X22 * L21 * X11) i j + (-(DeltaFirst * X11 + DeltaSecond)) i j) -
        (-(X22 * L21 * X11) i j) =
      (-(DeltaFirst * X11 + DeltaSecond)) i j
  ring

/-- Direct first-order composition of the two products.  This exact
operation-level form keeps the norm of the computed first product `That`.
The next theorem eliminates it to first order. -/
theorem Higham14Problem142Method2BStepSpec.updateDelta_firstOrder {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond : ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond) :
    FirstOrderLe u
      ((cFirst * u * maxEntryNormRect hm hm X22 *
          maxEntryNormRect hm hr L21) *
          ((r : ℝ) * maxEntryNormRect hr hr X11) +
        cSecond * u * maxEntryNormRect hm hr That *
          maxEntryNormRect hr hr X11)
      (maxEntryNormRect hm hr
        (higham14_problem14_2_method2B_updateDelta
          DeltaFirst X11 DeltaSecond)) := by
  have hFirstPropagated :=
    higham14_problem14_2_firstOrder_mul_right hm hr hr u
      (cFirst * u * maxEntryNormRect hm hm X22 *
        maxEntryNormRect hm hr L21)
      DeltaFirst X11 h.first_product.norm_bound
  apply FirstOrderLe.add hFirstPropagated h.second_product.norm_bound
  simp only [higham14_problem14_2_method2B_updateDelta]
  calc
    maxEntryNormRect hm hr (-(DeltaFirst * X11 + DeltaSecond)) =
        maxEntryNormRect hm hr (DeltaFirst * X11 + DeltaSecond) :=
      higham14_problem14_2_maxEntryNormRect_neg hm hr _
    _ ≤ maxEntryNormRect hm hr (DeltaFirst * X11) +
        maxEntryNormRect hm hr DeltaSecond :=
      higham14_problem14_2_maxEntryNormRect_add_le hm hr _ _

/-- Source-shaped leading term for the two-product update.  The coefficients
`r*cFirst` and `m*cSecond` are the max-entry-norm dimension costs of the two
matrix products. -/
noncomputable def higham14_problem14_2_method2B_updateLeading {r m : ℕ}
    (u cFirst cSecond normX22 normL21 normX11 : ℝ) : ℝ :=
  ((r : ℝ) * cFirst + (m : ℝ) * cSecond) * u *
    normX22 * normL21 * normX11

/-- Eliminating the computed intermediate `That` introduces only a
second-order remainder.  This is the arbitrary-(13.4) two-product analogue of
Higham's `Delta(X22,L21,X11)` notation. -/
theorem Higham14Problem142Method2BStepSpec.updateDelta_source_firstOrder
    {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond : ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcFirst : 0 ≤ cFirst) (hcSecond : 0 ≤ cSecond) :
    FirstOrderLe u
      (higham14_problem14_2_method2B_updateLeading (r := r) (m := m)
        u cFirst cSecond
        (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
        (maxEntryNormRect hr hr X11))
      (maxEntryNormRect hm hr
        (higham14_problem14_2_method2B_updateDelta
          DeltaFirst X11 DeltaSecond)) := by
  let a := maxEntryNormRect hm hm X22
  let b := maxEntryNormRect hm hr L21
  let x := maxEntryNormRect hr hr X11
  let t := maxEntryNormRect hm hr That
  let dFirst := maxEntryNormRect hm hr DeltaFirst
  let dSecond := maxEntryNormRect hm hr DeltaSecond
  let dUpdate := maxEntryNormRect hm hr
    (higham14_problem14_2_method2B_updateDelta DeltaFirst X11 DeltaSecond)
  have ha : 0 ≤ a := maxEntryNormRect_nonneg hm hm X22
  have hb : 0 ≤ b := maxEntryNormRect_nonneg hm hr L21
  have hx : 0 ≤ x := maxEntryNormRect_nonneg hr hr X11
  have ht : 0 ≤ t := maxEntryNormRect_nonneg hm hr That
  have hdFirst : 0 ≤ dFirst := maxEntryNormRect_nonneg hm hr DeltaFirst
  have hdSecond : 0 ≤ dSecond := maxEntryNormRect_nonneg hm hr DeltaSecond
  have hFirst : FirstOrderLe u (cFirst * u * a * b) dFirst := by
    simpa [a, b, dFirst] using h.first_product.norm_bound
  have hSecond : FirstOrderLe u (cSecond * u * t * x) dSecond := by
    simpa [t, x, dSecond] using h.second_product.norm_bound
  rcases hFirst with ⟨KFirst, hKFirst, hFirstBound⟩
  rcases hSecond with ⟨KSecond, hKSecond, hSecondBound⟩
  have hProduct :
      maxEntryNormRect hm hr (X22 * L21) ≤ (m : ℝ) * a * b := by
    simpa [a, b, rectMatMul, Matrix.mul_apply] using
      maxEntryNormRect_rectMatMul_le hm hm hr X22 L21
  have hThat : t ≤ (m : ℝ) * a * b + dFirst := by
    rw [show t = maxEntryNormRect hm hr That by rfl,
      h.first_product.equation]
    calc
      maxEntryNormRect hm hr (X22 * L21 + DeltaFirst) ≤
          maxEntryNormRect hm hr (X22 * L21) + dFirst := by
        simpa [dFirst] using
          higham14_problem14_2_maxEntryNormRect_add_le hm hr
            (X22 * L21) DeltaFirst
      _ ≤ (m : ℝ) * a * b + dFirst := add_le_add hProduct le_rfl
  have hUpdate : dUpdate ≤ (r : ℝ) * dFirst * x + dSecond := by
    have hMul :
        maxEntryNormRect hm hr (DeltaFirst * X11) ≤
          (r : ℝ) * dFirst * x := by
      simpa [dFirst, x, rectMatMul, Matrix.mul_apply] using
        maxEntryNormRect_rectMatMul_le hm hr hr DeltaFirst X11
    calc
      dUpdate = maxEntryNormRect hm hr
          (-(DeltaFirst * X11 + DeltaSecond)) := by
        rfl
      _ = maxEntryNormRect hm hr (DeltaFirst * X11 + DeltaSecond) :=
        higham14_problem14_2_maxEntryNormRect_neg hm hr _
      _ ≤ maxEntryNormRect hm hr (DeltaFirst * X11) + dSecond := by
        simpa [dSecond] using
          higham14_problem14_2_maxEntryNormRect_add_le hm hr
            (DeltaFirst * X11) DeltaSecond
      _ ≤ (r : ℝ) * dFirst * x + dSecond := add_le_add hMul le_rfl
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcu : 0 ≤ cSecond * u := mul_nonneg hcSecond hu0
  have hFirstScaled :
      (r : ℝ) * dFirst * x ≤
        (r : ℝ) * (cFirst * u * a * b + KFirst * u ^ 2) * x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFirstBound hr0) hx
  have hThatScaled :
      cSecond * u * t * x ≤
        cSecond * u * ((m : ℝ) * a * b + dFirst) * x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hThat hcu) hx
  have hFirstNested :
      cSecond * u * dFirst * x ≤
        cSecond * u * (cFirst * u * a * b + KFirst * u ^ 2) * x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFirstBound hcu) hx
  have hu3 : u ^ 3 ≤ u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hCubic :
      (cSecond * KFirst * x) * u ^ 3 ≤
        (cSecond * KFirst * x) * u ^ 2 := by
    exact mul_le_mul_of_nonneg_left hu3
      (mul_nonneg (mul_nonneg hcSecond hKFirst) hx)
  let K := (r : ℝ) * KFirst * x + cSecond * cFirst * a * b * x +
    cSecond * KFirst * x + KSecond
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  change dUpdate ≤
    higham14_problem14_2_method2B_updateLeading (r := r) (m := m)
      u cFirst cSecond a b x +
      K * u ^ 2
  calc
    dUpdate ≤ (r : ℝ) * dFirst * x + dSecond := hUpdate
    _ ≤ (r : ℝ) * (cFirst * u * a * b + KFirst * u ^ 2) * x +
        (cSecond * u * t * x + KSecond * u ^ 2) :=
      add_le_add hFirstScaled hSecondBound
    _ ≤ (r : ℝ) * (cFirst * u * a * b + KFirst * u ^ 2) * x +
        (cSecond * u * ((m : ℝ) * a * b + dFirst) * x +
          KSecond * u ^ 2) := by
      linarith [hThatScaled]
    _ ≤ (r : ℝ) * (cFirst * u * a * b + KFirst * u ^ 2) * x +
        (cSecond * u * ((m : ℝ) * a * b +
            (cFirst * u * a * b + KFirst * u ^ 2)) * x +
          KSecond * u ^ 2) := by
      nlinarith [hFirstNested]
    _ ≤ higham14_problem14_2_method2B_updateLeading (r := r) (m := m)
        u cFirst cSecond a b x +
        K * u ^ 2 := by
      dsimp [higham14_problem14_2_method2B_updateLeading, K]
      nlinarith [hCubic]

/-! ### Left-residual obstruction -/

/-- The exact Method 2B off-diagonal residual identity under a right-oriented
(13.5) diagonal-block certificate.  Both terms on the right are derived
operation errors. -/
theorem Higham14Problem142Method2BStepSpec.offdiag_residual_equation
    {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond cDiag : ℝ}
    {L11 X11 Delta11 : Matrix (Fin r) (Fin r) ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : RightTriangularSolveFirstOrderSpec u cDiag
      (maxEntryNormRect hr hr L11) (maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr Delta11)
      L11 (1 : Matrix (Fin r) (Fin r) ℝ) Delta11 X11) :
    X21 * L11 + X22 * L21 =
      higham14_problem14_2_method2B_updateDelta DeltaFirst X11 DeltaSecond * L11 -
        (X22 * L21) * Delta11 := by
  rw [h.update_equation]
  rw [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc, hDiag.equation,
    Matrix.mul_add, Matrix.mul_one]
  abel

/-- The leading residual term forced by the arbitrary Chapter 13 operation
models.  Its final factor is exactly the uncontrolled block product
`norm(X11) * norm(L11)` identified in Higham's Method 2B discussion. -/
noncomputable def higham14_problem14_2_method2B_uncontrolledLeading {r m : ℕ}
    (u cFirst cSecond cDiag normX22 normL21 normX11 normL11 : ℝ) : ℝ :=
  ((r : ℝ) * ((r : ℝ) * cFirst + (m : ℝ) * cSecond) +
      (r : ℝ) * (m : ℝ) * cDiag) *
    u * normX22 * normL21 * (normX11 * normL11)

/-- Problem 14.2, Method 2B: the two (13.4) products and the (13.5)
diagonal-block relation imply a first-order left-residual estimate, but the
estimate necessarily retains `norm(X11) * norm(L11)`.  No desired residual
bound is a premise. -/
theorem Higham14Problem142Method2BStepSpec.offdiag_residual_firstOrder
    {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cFirst cSecond cDiag : ℝ}
    {L11 X11 Delta11 : Matrix (Fin r) (Fin r) ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : RightTriangularSolveFirstOrderSpec u cDiag
      (maxEntryNormRect hr hr L11) (maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr Delta11)
      L11 (1 : Matrix (Fin r) (Fin r) ℝ) Delta11 X11)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcFirst : 0 ≤ cFirst) (hcSecond : 0 ≤ cSecond)
    (hcDiag : 0 ≤ cDiag) :
    FirstOrderLe u
      (higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
        u cFirst cSecond cDiag
        (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
        (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11))
      (maxEntryNormRect hm hr (X21 * L11 + X22 * L21)) := by
  let updateLeading :=
    higham14_problem14_2_method2B_updateLeading (r := r) (m := m)
      u cFirst cSecond
      (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
      (maxEntryNormRect hr hr X11)
  have hUpdate := h.updateDelta_source_firstOrder hu0 hu1 hcFirst hcSecond
  have hUpdatePropagated :=
    higham14_problem14_2_firstOrder_mul_right hm hr hr u updateLeading
      (higham14_problem14_2_method2B_updateDelta DeltaFirst X11 DeltaSecond)
      L11 (by simpa [updateLeading] using hUpdate)
  have hDiagPropagated :=
    higham14_problem14_2_firstOrder_mul_left hm hr hr u
      (cDiag * u * maxEntryNormRect hr hr L11 *
        maxEntryNormRect hr hr X11)
      (X22 * L21) Delta11 hDiag.norm_bound
  have hProduct :
      maxEntryNormRect hm hr (X22 * L21) ≤
        (m : ℝ) * maxEntryNormRect hm hm X22 *
          maxEntryNormRect hm hr L21 := by
    simpa [rectMatMul, Matrix.mul_apply] using
      maxEntryNormRect_rectMatMul_le hm hm hr X22 L21
  have hDiagLeadingNonneg :
      0 ≤ cDiag * u * maxEntryNormRect hr hr L11 *
        maxEntryNormRect hr hr X11 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hcDiag hu0)
        (maxEntryNormRect_nonneg hr hr L11))
      (maxEntryNormRect_nonneg hr hr X11)
  have hScale :
      (r : ℝ) * maxEntryNormRect hm hr (X22 * L21) ≤
        (r : ℝ) * ((m : ℝ) * maxEntryNormRect hm hm X22 *
          maxEntryNormRect hm hr L21) := by
    exact mul_le_mul_of_nonneg_left hProduct (Nat.cast_nonneg r)
  have hDiagSource := hDiagPropagated.mono_leading
    (mul_le_mul_of_nonneg_left hScale hDiagLeadingNonneg)
  have hValue :
      maxEntryNormRect hm hr (X21 * L11 + X22 * L21) ≤
        maxEntryNormRect hm hr
          (higham14_problem14_2_method2B_updateDelta
            DeltaFirst X11 DeltaSecond * L11) +
        maxEntryNormRect hm hr ((X22 * L21) * Delta11) := by
    rw [h.offdiag_residual_equation hDiag]
    calc
      maxEntryNormRect hm hr
          (higham14_problem14_2_method2B_updateDelta
              DeltaFirst X11 DeltaSecond * L11 - (X22 * L21) * Delta11) =
          maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
                DeltaFirst X11 DeltaSecond * L11 +
              -((X22 * L21) * Delta11)) := by rw [sub_eq_add_neg]
      _ ≤ maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              DeltaFirst X11 DeltaSecond * L11) +
          maxEntryNormRect hm hr (-((X22 * L21) * Delta11)) :=
        higham14_problem14_2_maxEntryNormRect_add_le hm hr _ _
      _ = maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              DeltaFirst X11 DeltaSecond * L11) +
          maxEntryNormRect hm hr ((X22 * L21) * Delta11) := by
        exact congrArg
          (fun z => maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              DeltaFirst X11 DeltaSecond * L11) + z)
          (higham14_problem14_2_maxEntryNormRect_neg hm hr
            ((X22 * L21) * Delta11))
  have hCombined := FirstOrderLe.add hUpdatePropagated hDiagSource hValue
  have hLeading :
      updateLeading * ((r : ℝ) * maxEntryNormRect hr hr L11) +
          (cDiag * u * maxEntryNormRect hr hr L11 *
              maxEntryNormRect hr hr X11) *
            ((r : ℝ) * ((m : ℝ) * maxEntryNormRect hm hm X22 *
              maxEntryNormRect hm hr L21)) =
        higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
          u cFirst cSecond cDiag
          (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
          (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11) := by
    simp only [updateLeading, higham14_problem14_2_method2B_updateLeading,
      higham14_problem14_2_method2B_uncontrolledLeading]
    ring
  rw [← hLeading]
  exact hCombined

/-- Two-block integration with the recursive composer from
`Ch14Problem142`.  The diagonal and off-diagonal estimates are operation
derived; only the trailing recursive estimate is supplied. -/
theorem higham14_problem14_2_method2B_twoBlock_left_firstOrder
    {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m)
    (u cFirst cSecond cDiag leading22 : ℝ)
    (L11 X11 Delta11 : Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
    (That Phat DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ)
    (hStep : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : RightTriangularSolveFirstOrderSpec u cDiag
      (maxEntryNormRect hr hr L11) (maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr Delta11)
      L11 (1 : Matrix (Fin r) (Fin r) ℝ) Delta11 X11)
    (h22 : FirstOrderLe u leading22
      (maxEntryNormRect hm hm
        (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcFirst : 0 ≤ cFirst) (hcSecond : 0 ≤ cSecond)
    (hcDiag : 0 ≤ cDiag) :
    FirstOrderLe u
      (max
        (cDiag * u * maxEntryNormRect hr hr L11 *
          maxEntryNormRect hr hr X11)
        (max
          (higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
            u cFirst cSecond cDiag
            (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
            (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11))
          leading22))
      (maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock X11 X21 X22 *
          higham14_problem14_2_lowerBlock L11 L21 L22 -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have h11 : FirstOrderLe u
      (cDiag * u * maxEntryNormRect hr hr L11 *
        maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr
        (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))) := by
    have hEq : X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ) = Delta11 := by
      rw [hDiag.equation]
      abel
    rw [hEq]
    exact hDiag.norm_bound
  have h21 := hStep.offdiag_residual_firstOrder hDiag hu0 hu1
    hcFirst hcSecond hcDiag
  rw [higham14_problem14_2_lowerBlock_mul_sub_one]
  exact higham14_problem14_2_lowerBlock_residual_firstOrder hr hm u
    (cDiag * u * maxEntryNormRect hr hr L11 *
      maxEntryNormRect hr hr X11)
    (higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
      u cFirst cSecond cDiag
      (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
      (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11))
    leading22
    (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))
    (X21 * L11 + X22 * L21)
    (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 h21 h22

end NumStability.Ch14Ext
