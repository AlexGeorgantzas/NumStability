-- Exact algorithm specifications for Higham, 2nd ed., Chapter 20.

import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators

/-! ## Section 20.5: direct least-squares iterative refinement -/

/-- Step 1 of Higham's direct least-squares refinement: form `r = b - A*x`. -/
noncomputable def higham20DirectLSRefinementResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  lsResidualHigham A b x

/-- Step 3 of Higham's direct least-squares refinement: form `y = x + d`. -/
noncomputable def higham20DirectLSRefinementUpdate {n : ℕ}
    (x d : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j + d j

/-- Translating the correction problem by the current iterate preserves the
least-squares residual exactly. -/
theorem higham20_directLSRefinement_residual_translation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsResidual A (higham20DirectLSRefinementResidual A b x) d =
      lsResidual A b (higham20DirectLSRefinementUpdate x d) := by
  ext i
  unfold lsResidual higham20DirectLSRefinementResidual
    higham20DirectLSRefinementUpdate lsResidualHigham
  rw [congrFun (rectMatMulVec_add A x d) i]
  ring

/-- The correction objective in step 2 is the original objective evaluated at
the updated iterate. -/
theorem higham20_directLSRefinement_objective_translation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsObjective A (higham20DirectLSRefinementResidual A b x) d =
      lsObjective A b (higham20DirectLSRefinementUpdate x d) := by
  unfold lsObjective
  rw [higham20_directLSRefinement_residual_translation A b x d]

/-- An exact solve of the correction least-squares problem makes the updated
iterate an exact minimizer of the original problem. -/
theorem higham20_directLSRefinement_update_isLeastSquaresMinimizer {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ)
    (hd : IsLeastSquaresMinimizer
      A (higham20DirectLSRefinementResidual A b x) d) :
    IsLeastSquaresMinimizer A b (higham20DirectLSRefinementUpdate x d) := by
  intro y
  let e : Fin n → ℝ := fun j => y j - x j
  have hupdate_e : higham20DirectLSRefinementUpdate x e = y := by
    ext j
    simp [higham20DirectLSRefinementUpdate, e]
  calc
    lsObjective A b (higham20DirectLSRefinementUpdate x d) =
        lsObjective A (higham20DirectLSRefinementResidual A b x) d :=
      (higham20_directLSRefinement_objective_translation A b x d).symm
    _ ≤ lsObjective A (higham20DirectLSRefinementResidual A b x) e := hd e
    _ = lsObjective A b (higham20DirectLSRefinementUpdate x e) :=
      higham20_directLSRefinement_objective_translation A b x e
    _ = lsObjective A b y := by rw [hupdate_e]

/-- The three displayed steps of the direct refinement scheme on one iterate:
form the residual, solve its least-squares correction problem, and update. -/
structure Higham20DirectLSRefinementStep {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (d y : Fin n → ℝ) : Prop where
  residual_eq : r = higham20DirectLSRefinementResidual A b x
  correction_minimizer : IsLeastSquaresMinimizer A r d
  update_eq : y = higham20DirectLSRefinementUpdate x d

theorem Higham20DirectLSRefinementStep.updated_isLeastSquaresMinimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {x : Fin n → ℝ} {r : Fin m → ℝ} {d y : Fin n → ℝ}
    (h : Higham20DirectLSRefinementStep A b x r d y) :
    IsLeastSquaresMinimizer A b y := by
  rw [h.update_eq]
  apply higham20_directLSRefinement_update_isLeastSquaresMinimizer A b x d
  simpa [h.residual_eq] using h.correction_minimizer

/-- A finite iteration-state object for repeating the three-step direct scheme.
The state at `k+1` is tied to the state at `k` by the displayed algorithm. -/
structure Higham20DirectLSRefinementRun {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (steps : ℕ) where
  iterate : Fin (steps + 1) → Fin n → ℝ
  residual : Fin steps → Fin m → ℝ
  correction : Fin steps → Fin n → ℝ
  step : ∀ k : Fin steps,
    Higham20DirectLSRefinementStep A b (iterate k.castSucc)
      (residual k) (correction k) (iterate k.succ)

theorem Higham20DirectLSRefinementRun.successor_isLeastSquaresMinimizer
    {m n steps : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    (run : Higham20DirectLSRefinementRun A b steps) (k : Fin steps) :
    IsLeastSquaresMinimizer A b (run.iterate k.succ) :=
  (run.step k).updated_isLeastSquaresMinimizer

/-! ## Section 20.5: augmented-system iterative refinement -/

/-- Top residual of the augmented system `[I A; A^T 0][r;x]=[b;0]`. -/
noncomputable def higham20AugmentedRefinementTopResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b r : Fin m → ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => b i - (r i + rectMatMulVec A x i)

/-- Bottom residual of the augmented system `[I A; A^T 0][r;x]=[b;0]`. -/
noncomputable def higham20AugmentedRefinementBottomResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) : Fin n → ℝ :=
  fun j => -∑ i : Fin m, A i j * r i

/-- One exact augmented-system refinement step.  The correction pair solves
the augmented system with the two block residuals, and both state components
are then updated. -/
structure Higham20AugmentedRefinementStep {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ)
    (rNext : Fin m → ℝ) (xNext : Fin n → ℝ) : Prop where
  correction_system : LSAugmentedSystem A
    (higham20AugmentedRefinementTopResidual A b r x)
    (higham20AugmentedRefinementBottomResidual A r) dr dx
  residual_update : rNext = fun i => r i + dr i
  solution_update : xNext = fun j => x j + dx j

/-- Exact augmented refinement annihilates the original augmented-system
residual in one step. -/
theorem Higham20AugmentedRefinementStep.updated_augmentedNormalSystem
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {r dr rNext : Fin m → ℝ} {x dx xNext : Fin n → ℝ}
    (h : Higham20AugmentedRefinementStep A b r x dr dx rNext xNext) :
    LSAugmentedNormalSystem A b rNext xNext := by
  constructor
  · intro i
    have hcorr := h.correction_system.1 i
    rw [h.residual_update, h.solution_update]
    have hmul := congrFun (rectMatMulVec_add A x dx) i
    rw [hmul]
    unfold higham20AugmentedRefinementTopResidual at hcorr
    linarith
  · intro j
    have hcorr := h.correction_system.2 j
    rw [h.residual_update]
    unfold higham20AugmentedRefinementBottomResidual at hcorr
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    linarith

/-- The updated solution component is therefore an exact least-squares
minimizer for the original data. -/
theorem Higham20AugmentedRefinementStep.updated_isLeastSquaresMinimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {r dr rNext : Fin m → ℝ} {x dx xNext : Fin n → ℝ}
    (h : Higham20AugmentedRefinementStep A b r x dr dx rNext xNext) :
    IsLeastSquaresMinimizer A b xNext := by
  have hsystem := h.updated_augmentedNormalSystem
  have hrNext : rNext = lsResidualHigham A b xNext := by
    ext i
    have hi := hsystem.1 i
    unfold lsResidualHigham
    linarith
  have hcanonical :
      LSAugmentedNormalSystem A b (lsResidualHigham A b xNext) xNext := by
    rw [← hrNext]
    exact hsystem
  have hnormal : RectLSNormalEquations A b xNext :=
    (LSAugmentedNormalSystem.iff_rectLSNormalEquations A b xNext).mp hcanonical
  exact hnormal.isLeastSquaresMinimizer

/-- A finite iteration-state object for augmented-system refinement. -/
structure Higham20AugmentedRefinementRun {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (steps : ℕ) where
  residualState : Fin (steps + 1) → Fin m → ℝ
  solutionState : Fin (steps + 1) → Fin n → ℝ
  residualCorrection : Fin steps → Fin m → ℝ
  solutionCorrection : Fin steps → Fin n → ℝ
  step : ∀ k : Fin steps,
    Higham20AugmentedRefinementStep A b
      (residualState k.castSucc) (solutionState k.castSucc)
      (residualCorrection k) (solutionCorrection k)
      (residualState k.succ) (solutionState k.succ)

theorem Higham20AugmentedRefinementRun.successor_augmentedNormalSystem
    {m n steps : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    (run : Higham20AugmentedRefinementRun A b steps) (k : Fin steps) :
    LSAugmentedNormalSystem A b
      (run.residualState k.succ) (run.solutionState k.succ) :=
  (run.step k).updated_augmentedNormalSystem

/-- The supplied-factor QR formulas `h = R^{-T}g`, `d = Q^T f`,
`dr = Q[h;d₂]`, and `dx = R^{-1}(d₁-h)` construct the correction field
of an augmented refinement step. -/
theorem Higham20AugmentedRefinementStep.of_exact_qr_correction
    {n k : ℕ}
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (b r : Fin (n + k) → ℝ) (x : Fin n → ℝ)
    (d1 h dx : Fin n → ℝ) (d2 : Fin k → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hd : matMulVec (n + k) (matTranspose Q)
        (higham20AugmentedRefinementTopResidual A b r x) = Fin.append d1 d2)
    (hRt : ∀ j : Fin n, ∑ i : Fin n, R i j * h i =
      higham20AugmentedRefinementBottomResidual A r j)
    (hRx : rectMatMulVec R dx = fun i : Fin n => d1 i - h i) :
    Higham20AugmentedRefinementStep A b r x
      (matMulVec (n + k) Q (Fin.append h d2)) dx
      (fun i => r i + matMulVec (n + k) Q (Fin.append h d2) i)
      (fun j => x j + dx j) := by
  constructor
  · exact LSAugmentedSystem.exact_qr_solution_of_factors
      Q A R (higham20AugmentedRefinementTopResidual A b r x)
      d1 h dx d2 (higham20AugmentedRefinementBottomResidual A r)
      hQ hA hd hRt hRx
  · rfl
  · rfl

/-! ## Section 20.6: seminormal and corrected seminormal equations -/

/-- The two triangular solves implementing `R^T R x = A^T b`: first solve
`R^T z = A^T b`, then solve `R x = z`. -/
structure Higham20SeminormalEquationsSolve {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) : Prop where
  transpose_solve : ∀ j : Fin n,
    ∑ i : Fin n, R i j * z i = rectLSRhs A b j
  triangular_solve : rectMatMulVec R x = z

/-- An exact tall QR relation `A = Q[R;0]` supplies the seminormal identity
`A^T A = R^T R`. -/
theorem higham20_qrFactorization_rectLSGram_eq_seminormalGram {n k : ℕ}
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    ∀ j s : Fin n,
      rectLSGram A j s = ∑ i : Fin n, R i j * R i s := by
  intro j s
  have hpreserve :=
    rectLSGram_matMulRectLeft_orthogonal Q (lsQRTallBlock R) hQ
  calc
    rectLSGram A j s =
        rectLSGram (matMulRectLeft Q (lsQRTallBlock R)) j s := by rw [hA]
    _ = rectLSGram (lsQRTallBlock R) j s :=
      congrFun (congrFun hpreserve j) s
    _ = ∑ i : Fin n, R i j * R i s := by
      unfold rectLSGram lsQRTallBlock
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]

/-- Two exact triangular solves satisfy the displayed seminormal equations. -/
theorem Higham20SeminormalEquationsSolve.seminormal_equations
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    (h : Higham20SeminormalEquationsSolve A b R z x) :
    ∀ j : Fin n,
      (∑ k : Fin n, (∑ i : Fin n, R i j * R i k) * x k) =
        rectLSRhs A b j := by
  intro j
  calc
    (∑ k : Fin n, (∑ i : Fin n, R i j * R i k) * x k) =
        ∑ k : Fin n, ∑ i : Fin n, (R i j * R i k) * x k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ k : Fin n, (R i j * R i k) * x k := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, R i j * rectMatMulVec R x i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold rectMatMulVec
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i : Fin n, R i j * z i := by rw [h.triangular_solve]
    _ = rectLSRhs A b j := h.transpose_solve j

/-- If the supplied QR factor has `A^T A = R^T R`, the two SNE solves satisfy
the original rectangular normal equations. -/
theorem Higham20SeminormalEquationsSolve.rectLSNormalEquations
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    (h : Higham20SeminormalEquationsSolve A b R z x)
    (hGram : ∀ j k : Fin n,
      rectLSGram A j k = ∑ i : Fin n, R i j * R i k) :
    RectLSNormalEquations A b x := by
  intro j
  unfold matMulVec
  simp_rw [hGram]
  exact h.seminormal_equations j

theorem Higham20SeminormalEquationsSolve.isLeastSquaresMinimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    (h : Higham20SeminormalEquationsSolve A b R z x)
    (hGram : ∀ j k : Fin n,
      rectLSGram A j k = ∑ i : Fin n, R i j * R i k) :
    IsLeastSquaresMinimizer A b x :=
  (h.rectLSNormalEquations hGram).isLeastSquaresMinimizer

/-- Source-facing SNE endpoint using the exact QR factors from which the
seminormal equations are derived. -/
theorem Higham20SeminormalEquationsSolve.isLeastSquaresMinimizer_of_qr
    {n k : ℕ}
    {Q : Fin (n + k) → Fin (n + k) → ℝ}
    {A : Fin (n + k) → Fin n → ℝ} {b : Fin (n + k) → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    (h : Higham20SeminormalEquationsSolve A b R z x)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    IsLeastSquaresMinimizer A b x :=
  h.isLeastSquaresMinimizer
    (higham20_qrFactorization_rectLSGram_eq_seminormalGram Q A R hQ hA)

/-- Higham's four displayed CSNE equations.  The two SNE equations retain
their two triangular-solve witnesses, and the residual is explicitly formed as
`b - A*x` before the correction solve. -/
structure Higham20CorrectedSeminormalEquationsStep {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ)
    (z x : Fin n → ℝ) (r : Fin m → ℝ)
    (t w y : Fin n → ℝ) : Prop where
  initial_sne : Higham20SeminormalEquationsSolve A b R z x
  residual_eq : r = higham20DirectLSRefinementResidual A b x
  correction_sne : Higham20SeminormalEquationsSolve A r R t w
  update_eq : y = higham20DirectLSRefinementUpdate x w

theorem Higham20CorrectedSeminormalEquationsStep.initial_isLeastSquaresMinimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    {r : Fin m → ℝ} {t w y : Fin n → ℝ}
    (h : Higham20CorrectedSeminormalEquationsStep A b R z x r t w y)
    (hGram : ∀ j k : Fin n,
      rectLSGram A j k = ∑ i : Fin n, R i j * R i k) :
    IsLeastSquaresMinimizer A b x :=
  h.initial_sne.isLeastSquaresMinimizer hGram

/-- The exact four-step CSNE update is an exact least-squares minimizer. -/
theorem Higham20CorrectedSeminormalEquationsStep.updated_isLeastSquaresMinimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    {r : Fin m → ℝ} {t w y : Fin n → ℝ}
    (h : Higham20CorrectedSeminormalEquationsStep A b R z x r t w y)
    (hGram : ∀ j k : Fin n,
      rectLSGram A j k = ∑ i : Fin n, R i j * R i k) :
    IsLeastSquaresMinimizer A b y := by
  have hcorr : IsLeastSquaresMinimizer A r w :=
    h.correction_sne.isLeastSquaresMinimizer hGram
  rw [h.update_eq]
  apply higham20_directLSRefinement_update_isLeastSquaresMinimizer A b x w
  simpa [h.residual_eq] using hcorr

/-- Source-facing CSNE endpoint using the exact QR factors that determine
`R`. -/
theorem Higham20CorrectedSeminormalEquationsStep.updated_isLeastSquaresMinimizer_of_qr
    {n k : ℕ}
    {Q : Fin (n + k) → Fin (n + k) → ℝ}
    {A : Fin (n + k) → Fin n → ℝ} {b : Fin (n + k) → ℝ}
    {R : Fin n → Fin n → ℝ} {z x : Fin n → ℝ}
    {r : Fin (n + k) → ℝ} {t w y : Fin n → ℝ}
    (h : Higham20CorrectedSeminormalEquationsStep A b R z x r t w y)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R)) :
    IsLeastSquaresMinimizer A b y :=
  h.updated_isLeastSquaresMinimizer
    (higham20_qrFactorization_rectLSGram_eq_seminormalGram Q A R hQ hA)

end NumStability
