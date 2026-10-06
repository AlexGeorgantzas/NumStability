import NumStability.Algorithms.HighamChapter10

namespace NumStability

open scoped BigOperators

/-! # Higham Theorem 10.6: actual rounded Cholesky source closure

This file connects the source-shaped estimate already proved in
`HighamChapter10` to the concrete Algorithm 10.2 factor and the concrete two
triangular solves.  In particular, the perturbation, inverse, and norm
certificates are constructed here rather than accepted as endpoint premises.
-/

/-- The source diagonal scaling `H = D⁻¹ A D⁻¹`, with
`D = diag(sqrt (aᵢᵢ))`. -/
noncomputable def higham10SourceScaledMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j / (Real.sqrt (A i i) * Real.sqrt (A j j))

/-- The literal spectral condition number used in Theorem 10.6. -/
noncomputable def higham10SourceKappa2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  let H := higham10SourceScaledMatrix A
  opNorm2 H * opNorm2 (nonsingInv n H)

theorem higham10SourceScaledMatrix_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    IsSymPosDef n (higham10SourceScaledMatrix A) := by
  let dInv : Fin n → ℝ := fun i => (Real.sqrt (A i i))⁻¹
  have hdInv : ∀ i : Fin n, 0 < dInv i := by
    intro i
    exact inv_pos.mpr (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i))
  have hcong := isSymPosDef_diagCongr n dInv A hdInv hSPD
  have heq : (fun i j => dInv i * A i j * dInv j) =
      higham10SourceScaledMatrix A := by
    funext i j
    have hi : Real.sqrt (A i i) ≠ 0 :=
      (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i)).ne'
    have hj : Real.sqrt (A j j) ≠ 0 :=
      (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD j)).ne'
    simp only [dInv, higham10SourceScaledMatrix]
    field_simp [hi, hj]
  rwa [heq] at hcong

theorem higham10SourceScaledMatrix_diag {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) (i : Fin n) :
    higham10SourceScaledMatrix A i i = 1 := by
  have hs : Real.sqrt (A i i) ≠ 0 :=
    (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i)).ne'
  have hsquare : Real.sqrt (A i i) * Real.sqrt (A i i) = A i i := by
    nlinarith [Real.sq_sqrt (le_of_lt (higham10_spd_diag_pos A hSPD i))]
  rw [higham10SourceScaledMatrix, hsquare]
  exact div_self (ne_of_gt (higham10_spd_diag_pos A hSPD i))

/-- The canonical inverse of the scaled SPD matrix acts as a left inverse on
vectors. -/
theorem higham10SourceScaledMatrix_nonsingInv_action {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    (v : Fin n → ℝ) :
    matMulVec n (nonsingInv n (higham10SourceScaledMatrix A))
        (matMulVec n (higham10SourceScaledMatrix A) v) = v := by
  let H := higham10SourceScaledMatrix A
  have hHspd : IsSymPosDef n H := by
    simpa [H] using higham10SourceScaledMatrix_isSymPosDef A hSPD
  have hleft : IsLeftInverse n H (nonsingInv n H) :=
    (isInverse_nonsingInv_of_det_ne_zero n H
      (isSymPosDef_det_ne_zero H hHspd)).1
  have hmat : matMul n (nonsingInv n H) H = idMatrix n := by
    funext i j
    exact hleft i j
  have haction :
      matMulVec n (nonsingInv n H) (matMulVec n H v) = v := by
    funext i
    rw [← matMulVec_matMul n (nonsingInv n H) H v i, hmat]
    exact congrFun (matMulVec_id n v) i
  simpa [H] using haction

/-- The inverse operator norm is bounded by the literal condition number.
The positive dimension assumption supplies a unit diagonal entry of the scaled
matrix, hence `1 ≤ ‖H‖₂`. -/
theorem higham10SourceScaledMatrix_inverse_opNorm2Le_kappa2 {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    opNorm2Le (nonsingInv n (higham10SourceScaledMatrix A))
      (higham10SourceKappa2 A) := by
  let H := higham10SourceScaledMatrix A
  let Hinv := nonsingInv n H
  let i0 : Fin n := ⟨0, hn⟩
  have hH1 : 1 ≤ opNorm2 H := by
    have hdiag := diag_le_opNorm2Le H (opNorm2 H) (opNorm2Le_opNorm2 H) i0
    simpa [H, i0, higham10SourceScaledMatrix_diag A hSPD i0] using hdiag
  have hInv0 : 0 ≤ opNorm2 Hinv := opNorm2_nonneg Hinv
  have hnorm : opNorm2 Hinv ≤ opNorm2 H * opNorm2 Hinv := by
    nlinarith
  intro v
  calc
    vecNorm2 (matMulVec n Hinv v)
        ≤ opNorm2 Hinv * vecNorm2 v := opNorm2Le_opNorm2 Hinv v
    _ ≤ (opNorm2 H * opNorm2 Hinv) * vecNorm2 v :=
      mul_le_mul_of_nonneg_right hnorm (vecNorm2_nonneg v)
    _ = higham10SourceKappa2 A * vecNorm2 v := by
      simp [higham10SourceKappa2, H, Hinv]

/-- **Theorem 10.6, actual source closure.**

For an SPD input, a successful concrete Algorithm 10.2 run and its two
concrete rounded triangular solves produce Higham's displayed scaled forward
error bound with

`ε = n γ_(3n+1) / (1 - γ_(n+1))`

and the literal spectral condition number of `H = D⁻¹ A D⁻¹`.  No
factorization-error, solve-error, inverse-action, or operator-norm certificate
is an input to this theorem. -/
theorem higham10_6_actual_source_closed (fp : FPModel) (n : ℕ)
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (b x : Fin n → ℝ)
    (hSPD : IsSymPosDef n A)
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hgamma1 : gamma fp (n + 1) < 1)
    (hsuccess : ∀ j : Fin n, 0 < fl_cholPivot fp n A j)
    (hAx : matMulVec n A x = b)
    (hsmall : higham10SourceKappa2 A *
      ((n : ℝ) * (gamma fp (3 * n + 1) /
        (1 - gamma fp (n + 1)))) < 1) :
    let Rhat := fl_cholesky fp n A
    let yhat := fl_forwardSub fp n (fun i j : Fin n => Rhat j i) b
    let xhat := fl_backSub fp n Rhat yhat
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      higham10SourceKappa2 A *
          ((n : ℝ) * (gamma fp (3 * n + 1) /
            (1 - gamma fp (n + 1)))) /
        (1 - higham10SourceKappa2 A *
          ((n : ℝ) * (gamma fp (3 * n + 1) /
            (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  let Rhat := fl_cholesky fp n A
  let yhat := fl_forwardSub fp n (fun i j : Fin n => Rhat j i) b
  let xhat := fl_backSub fp n Rhat yhat
  have hu : fp.u < 1 := by
    unfold gammaValid at hn1
    push_cast at hn1
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) fp.u_nonneg]
  have hdiag : ∀ j : Fin n, Rhat j j ≠ 0 := by
    intro j
    dsimp [Rhat]
    rw [fl_cholesky_diag_eq]
    exact (fl_sqrt_pos fp hu _ (by simpa [fl_cholPivot] using hsuccess j)).ne'
  have hchol : CholeskyBackwardError n A Rhat (gamma fp (n + 1)) := by
    exact fl_cholesky_backward_error fp n A hSPD.1 hn1
      (fun j => (hsuccess j).le) hdiag
  have hpkg := cholesky_solve_backward_error_expanded fp n A Rhat b hdiag hchol hn1
  change ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |Rhat k i| * |Rhat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * xhat j = b i) at hpkg
  obtain ⟨DeltaA, hDelta, hsolve⟩ := hpkg
  have hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n DeltaA xhat i = b i := by
    intro i
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using hsolve i
  have hInv := higham10SourceScaledMatrix_nonsingInv_action A hSPD
  have hkappa0 : 0 ≤ higham10SourceKappa2 A := by
    exact mul_nonneg (opNorm2_nonneg _) (opNorm2_nonneg _)
  have hkappa := higham10SourceScaledMatrix_inverse_opNorm2Le_kappa2 hn A hSPD
  exact higham10_6_fl_scaled_forward_error_source fp n A Rhat
    (nonsingInv n (higham10SourceScaledMatrix A)) DeltaA x xhat b
    (fun i => higham10_spd_diag_pos A hSPD i) hgamma1 hn3 hchol hDelta
    hInv (higham10SourceKappa2 A) hkappa0 hkappa hAx hAhat hsmall

end NumStability
