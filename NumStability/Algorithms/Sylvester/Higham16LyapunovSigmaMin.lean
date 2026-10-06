-- Algorithms/Sylvester/Higham16LyapunovSigmaMin.lean
--
-- Source-facing sigma-min wrappers for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.3, equation (16.27).

import NumStability.Analysis.InverseOpNorm2

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    a positive singular-value lower bound for the Lyapunov operator instantiates
    the Lyapunov condition-number predicate with the inverse-operator constant
    `M = 1 / sigma`.

    This is the sigma-min version of the safe condition wrapper. It uses
    `lyapunovInverseOpBound_of_sigmaMin`, so the supplied hypothesis is the
    operator lower bound itself, not a black-box inverse-bound certificate. -/
theorem lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound (n : ℕ)
    (A X : Fin n → Fin n → ℝ) (alpha gamma sigma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y)) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) := by
  have hInv := lyapunovInverseOpBound_of_sigmaMin n A sigma hsigma hSigmaMin
  have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
  exact lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
    A X alpha gamma (1 / sigma) halpha hgamma hMnn hX hInv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive singular-value lower bound on the Lyapunov operator gives the
    corresponding `SepLowerBound` for the Sylvester specialization
    `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer. The hypothesis is the
    operator lower-bound certificate itself, not rounded Schur arithmetic or a
    LAPACK-style estimator path. -/
theorem SepLowerBound_lyapunov_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hSigmaMin Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) sigma hsigma hSylv

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the Lyapunov sigma-min route to `SepLowerBound(A,-A^T)`. -/
theorem H16_eq16_26_SepLowerBound_lyapunov_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  exact SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive singular-value lower bound for the Lyapunov operator makes its
    exact kernel trivial.

    This is an operator-level invertibility consequence of the supplied
    sigma-min certificate. It does not assume a separate `SepLowerBound`
    certificate or a vectorized coefficient determinant. -/
theorem lyapunovOp_eq_zero_iff_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (Y : Fin n -> Fin n -> Real) :
    (forall i j, lyapunovOp n A Y i j = 0) <->
      forall i j, Y i j = 0 := by
  constructor
  · intro hYop
    have hOpNorm : frobNorm (lyapunovOp n A Y) = 0 :=
      (frobNorm_eq_zero_iff (lyapunovOp n A Y)).mpr hYop
    have hLower := hSigmaMin Y
    rw [hOpNorm] at hLower
    have hYnorm_nonneg : 0 <= frobNorm Y := frobNorm_nonneg Y
    have hYnorm : frobNorm Y = 0 := by
      nlinarith
    exact (frobNorm_eq_zero_iff Y).mp hYnorm
  · intro hY i j
    unfold lyapunovOp matMul
    simp [hY]

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a positive Lyapunov operator sigma-min certificate eliminates the separate
    `SepLowerBound` assumption in the local uniqueness API: two exact solutions
    of `A X + X A^T = C` are equal.

    Scope: exact arithmetic and certificate transfer only. Existence still
    depends on the vectorized finite-dimensional solve infrastructure. -/
theorem lyapunov_unique_solution_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (C X1 X2 : Fin n -> Fin n -> Real)
    (hX1 : forall i j, lyapunovOp n A X1 i j = C i j)
    (hX2 : forall i j, lyapunovOp n A X2 i j = C i j) :
    forall i j, X1 i j = X2 i j := by
  exact
    lyapunov_unique_solution_of_sep n A sigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      C X1 X2 hX1 hX2

/-- Higham, 2nd ed., Chapter 16.2.1 and 16.3, equations (16.26)-(16.27):
    under a positive Lyapunov operator sigma-min certificate, zero exact
    Lyapunov residual norm certifies that the residual-zero candidate is the
    unique exact solution.

    Scope: exact arithmetic and certificate transfer only. This removes the
    separate `SepLowerBound` assumption from the residual-zero uniqueness route;
    it does not construct the sigma-min certificate or model rounded residual
    arithmetic. -/
theorem lyapunov_solution_eq_of_residual_norm_zero_sigmaMin (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hResidual : frobNorm (lyapunovResidual n A C Xhat) = 0) :
    forall i j, X i j = Xhat i j := by
  have hResidual_entries :
      forall i j, lyapunovResidual n A C Xhat i j = 0 :=
    (frobNorm_eq_zero_iff (lyapunovResidual n A C Xhat)).mp hResidual
  have hXhat : forall i j, lyapunovOp n A Xhat i j = C i j := by
    intro i j
    have hzero := hResidual_entries i j
    unfold lyapunovResidual at hzero
    exact (sub_eq_zero.mp hzero).symm
  exact
    lyapunov_unique_solution_of_sigmaMin n A sigma hsigma hSigmaMin
      C X Xhat hExact hXhat

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the supplied Lyapunov operator sigma-min
    exact-kernel theorem. -/
alias H16_eq16_27_lyapunovOp_eq_zero_iff_of_sigmaMin :=
  lyapunovOp_eq_zero_iff_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for exact Lyapunov uniqueness from a supplied
    operator sigma-min certificate. -/
alias H16_eq16_27_lyapunov_unique_solution_of_sigmaMin :=
  lyapunov_unique_solution_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2.1 and 16.3, equations (16.26)-(16.27):
    source-numbered alias for residual-zero exact Lyapunov uniqueness from a
    supplied operator sigma-min certificate. -/
alias H16_eq16_27_lyapunov_solution_eq_of_residual_norm_zero_sigmaMin :=
  lyapunov_solution_eq_of_residual_norm_zero_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    in positive dimension, a supplied positive singular-value lower-bound
    certificate for the Lyapunov operator lower-bounds the exact infimum model
    of `sep(A, -A^T)`.

    Scope: exact arithmetic and certificate transfer only. This theorem does
    not construct `sigma` from spectral data or a numerical estimator. -/
theorem sylvesterSepInf_lyapunov_ge_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      hn

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the Lyapunov sigma-min lower bound on the exact `sep(A,-A^T)`
    infimum model. -/
theorem H16_eq16_26_sylvesterSepInf_lyapunov_ge_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact sylvesterSepInf_lyapunov_ge_of_sigmaMin n A sigma
    hn hsigma hSigmaMin

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    in positive dimension, a supplied positive singular-value lower-bound
    certificate for the Lyapunov operator makes the exact infimum model of
    `sep(A, -A^T)` strictly positive.

    Scope: exact arithmetic and certificate transfer only. This theorem does
    not construct `sigma` from spectral data, a Schur form, or a numerical
    estimator. -/
theorem sylvesterSepInf_lyapunov_pos_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    lt_of_lt_of_le hsigma
      (sylvesterSepInf_lyapunov_ge_of_sigmaMin n A sigma
        hn hsigma hSigmaMin)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for strict positivity of the Lyapunov exact `sep(A,-A^T)` infimum
    from a supplied positive Lyapunov operator sigma-min certificate. -/
theorem H16_eq16_26_sylvesterSepInf_lyapunov_pos_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact sylvesterSepInf_lyapunov_pos_of_sigmaMin n A sigma
    hn hsigma hSigmaMin

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    source-numbered alias for strict positivity of `sep(A, -A^T)` from a
    supplied positive Lyapunov operator sigma-min certificate. -/
theorem H16_eq16_27_sylvesterSepInf_lyapunov_pos_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    sylvesterSepInf_lyapunov_pos_of_sigmaMin n A sigma
      hn hsigma hSigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    a supplied positive singular-value lower-bound certificate for the
    Lyapunov operator instantiates the a posteriori residual-error bound.

    Scope: exact arithmetic and certificate transfer. The theorem does not
    construct `sigma` from spectral data or from a numerical estimator. -/
theorem lyapunov_aposteriori_bound_of_sigmaMin (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  by_cases hE_ne :
      Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)
  · have hExactSylv :
        forall i j,
          sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j := by
      intro i j
      rw [<- lyapunovOp_eq_sylvesterOp n A X]
      exact hExact i j
    have h :=
      sylvester_aposteriori_bound_of_sepLowerBound n A
        (fun i j => -matTranspose A i j) C X Xhat sigma
        (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
        hExactSylv hE_ne
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using h
  · have hE_sq :
        frobNormSq (fun i j => X i j - Xhat i j) = 0 :=
      Classical.not_not.mp hE_ne
    have hE :
        frobNorm (fun i j => X i j - Xhat i j) = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hE_sq]
    rw [hE]
    exact mul_nonneg (by positivity) (frobNorm_nonneg _)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total alias for the supplied sigma-min Lyapunov a posteriori
    residual-error bound.

    Scope: exact arithmetic and certificate transfer. -/
theorem lyapunov_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sigmaMin n A C X Xhat sigma
      hsigma hSigmaMin hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    relative a posteriori Lyapunov residual-error bound from a supplied
    positive singular-value lower-bound certificate for the Lyapunov operator.

    Scope: exact arithmetic and certificate transfer, divided by the norm of
    the exact Lyapunov solution. -/
theorem lyapunov_relative_aposteriori_bound_of_sigmaMin (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hAbs :=
    lyapunov_aposteriori_bound_of_sigmaMin n A C X Xhat sigma
      hsigma hSigmaMin hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the supplied sigma-min Lyapunov a posteriori
    residual-error bound. The underlying endpoint already handles zero error
    internally. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_sigmaMin :=
  lyapunov_aposteriori_bound_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative supplied sigma-min Lyapunov
    a posteriori residual-error bound. The absolute endpoint already handles
    zero error internally; the relative form still assumes `0 < ||X||_F`. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sigmaMin :=
  lyapunov_relative_aposteriori_bound_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative alias for the supplied sigma-min Lyapunov a posteriori
    residual-error bound.

    Scope: exact arithmetic and certificate transfer, divided by the positive
    Frobenius norm of the exact Lyapunov solution. -/
theorem lyapunov_relative_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  have hAbs :=
    lyapunov_aposteriori_bound_of_sigmaMin_total n A C X Xhat sigma
      hsigma hSigmaMin hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total supplied sigma-min Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sigmaMin_total n A C X Xhat sigma
      hsigma hSigmaMin hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative supplied sigma-min Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sigmaMin_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sigmaMin_total n
      A C X Xhat sigma hsigma hSigmaMin hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator.

    Scope: exact arithmetic and certificate transfer. This does not claim
    rounded arithmetic, automatic Schur production, or an estimator for
    `sigma`. -/
theorem lyapunov_perturbation_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      sigma hsigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total Frobenius Lyapunov perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator.

    Scope: exact arithmetic and certificate transfer. The total `SepLowerBound`
    source wrapper handles the zero perturbation case. -/
theorem lyapunov_perturbation_bound_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total supplied sigma-min Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_perturbation_bound_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSigmaMin
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator.

    Scope: exact arithmetic and certificate transfer. The conclusion is the
    relative form of the perturbation inequality under the displayed operator
    lower-bound certificate. -/
theorem lyapunov_relative_perturbation_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  have hDeltaB :
      frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      sigma hsigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    total relative Lyapunov perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator.

    Scope: exact arithmetic and certificate transfer, divided by the positive
    Frobenius norm of the exact Lyapunov solution. -/
theorem lyapunov_relative_perturbation_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sepLowerBound_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin)
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total relative supplied sigma-min Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_perturbation_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSigmaMin
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    raw first-order Lyapunov perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator.

    This exposes the condition-certificate conclusion before the later
    `sqrt 2` relative-budget specialization. -/
theorem lyapunov_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hSigmaMin)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the supplied sigma-min first-order Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    lyapunov_first_order_bound_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma
      halpha hgamma hsigma hX hSigmaMin hLin

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    sigma-min Lyapunov first-order perturbation bound. If the Lyapunov operator
    satisfies `sigma * ||Y||_F <= ||L(Y)||_F` for all `Y`, then the printed
    relative bound follows with
    `lyapunovCond_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied singular-value
    lower-bound certificate for `L`. The remaining unproved glue, documented in
    `InverseOpNorm2.lean`, is the automatic construction of this hypothesis from
    the concrete vec/Kronecker coefficient via a Frobenius/vec isometry. -/
theorem H16_eq16_27_lyapunov_condition_of_sigmaMin (n : ℕ)
    (A X DeltaA DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  have hCond :=
    lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hSigmaMin
  have hPsinn : 0 ≤ lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) := by
    unfold lyapunovCond_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ 2 * alpha * frobNorm X + gamma := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt halpha, le_of_lt hgamma, hXnn]
    positivity
  exact lyapunov_relative_first_order_bound_of_condition n
    A X DeltaA DeltaC DeltaX alpha gamma
    (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) eps
    hCond hX hPsinn halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator. -/
theorem lyapunov_relative_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative supplied sigma-min first-order
    Lyapunov perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    lyapunov_relative_first_order_bound_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaC hLin

end NumStability
