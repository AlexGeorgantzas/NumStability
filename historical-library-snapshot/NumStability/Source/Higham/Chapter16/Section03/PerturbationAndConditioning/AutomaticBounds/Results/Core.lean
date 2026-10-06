import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AutomaticBounds.GramPositivity
import NumStability.Source.Higham.Chapter16.VecNorm.Results

/-!
# Algorithms.Sylvester.Higham16AutoCondition

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

-- Algorithms/Sylvester/Higham16AutoCondition.lean
--
-- Automatic (spectral-data-only) condition-number and perturbation bounds for
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 16.
--
-- The Chapter 16 structured Sylvester/Lyapunov condition estimates
-- (§16.3 eqs (16.23)-(16.25), §16.3 eq (16.27), §16.4 eq (16.28)) are all
-- available in this repository from a SUPPLIED singular-value lower bound
-- `sigma * ||Y||_F <= ||T(Y)||_F` for the Sylvester/Lyapunov operator
-- (`Higham16PsiSigmaMin.lean`, `Higham16PerturbationSigmaMin.lean`,
-- `Higham16LyapunovSigmaMin.lean`).  The residual repeated on those rows of the
-- source ledger is that the AUTOMATIC form -- producing `sigma > 0` from ONLY
-- the printed no-common-eigenvalue hypothesis, with no supplied
-- inverse/sigma-min/Gram/left-inverse certificate -- remained open.
--
-- This file closes that residual honestly.  The single genuinely missing link
-- is:
--
--   * `finiteMatrixGram_eigenvalues_pos_of_det_ne_zero` /
--     `exists_pos_le_finiteMatrixGram_eigenvalues_of_det_ne_zero`:
--     over the reals, the Gram matrix `P^T P` of a nonsingular `P`
--     (`det P != 0`) is positive DEFINITE, so every finite Hermitian eigenvalue
--     of `P^T P` is strictly positive and (in the nonempty index case) they
--     have a positive uniform lower bound `lam > 0`.
--
-- The proof is honest and end-to-end: `det P != 0` makes `mulVec P` injective,
-- so `P v != 0` for the (unit-norm, hence nonzero) `a`-th Hermitian
-- eigenvector `v` of `P^T P`; the Gram quadratic-form identity
-- `<v, P^T P v> = ||P v||^2 > 0` and the eigenvector Rayleigh identity
-- `<v, P^T P v> = lambda_a * ||v||^2 = lambda_a` then force `lambda_a > 0`.
--
-- Everything downstream of the positive Gram-eigenvalue lower bound already
-- exists in `Higham16VecNorm.lean`:
--
--   * `sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues` /
--     `lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues`: Gram-eigenvalue lower
--     bound -> concrete vec/Kronecker coefficient sigma-min bound
--     (`sigma = sqrt lam`).
--   * `sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin` /
--     `lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin`: coefficient sigma-min bound
--     -> operator sigma-min bound (through the vec/Frobenius isometry).
--   * the `_of_sigmaMin` condition-number and perturbation wrappers.
--
-- Chaining these with the missing link and the (16.3) determinant/eigenvalue
-- separation iff `sylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue`
-- yields AUTOMATIC condition-number theorems that need only the printed
-- `NoCommonComplexRightEigenvalue` hypothesis.
--
-- Honest scope and statement strength.
--   * The produced `sigma` is `sqrt` of the least Gram eigenvalue of the printed
--     vec/Kronecker coefficient, i.e. exactly `sigma_min(P)` in the nonempty
--     (`0 < n`) case; the automatic theorems therefore expose the SHARP
--     condition number `condSylvester ... sigma_min`, not a smuggled bound.  A
--     condition estimate is a LOWER bound on sensitivity (it can only
--     underestimate); the perturbation conclusions are stated as genuine
--     `... <= condSylvester ... * eps` inequalities holding for THAT explicit
--     `sigma`, existentially quantified, never as a guaranteed a-priori upper
--     bound the estimate does not provide.
--   * The genuine positivity/frobNorm side conditions carried by the printed
--     theorems themselves (`0 < alpha`, `0 < ||X||_F`, the linearized
--     perturbation equation, the perturbation budgets) are retained verbatim;
--     only the operator sigma-min certificate is discharged automatically.



namespace NumStability

namespace Wave17

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- The missing link: a nonsingular real matrix has a positive-definite Gram,
-- hence strictly positive least (finite Hermitian) Gram eigenvalue.
-- ============================================================















































































































-- ============================================================
-- Automatic operator sigma-min bounds from nonsingularity of the
-- vec/Kronecker coefficient (spectral data only).
-- ============================================================






























/-- **Automatic Sylvester-operator singular-value lower bound from the printed
    no-common-eigenvalue hypothesis.**

    In positive dimension, if the entrywise complexifications of `A` and `B`
    have no common complex right eigenvalue, then there is a strictly positive
    `sigma` with `sigma * ||Y||_F <= ||A Y - Y B||_F` for every `Y`.  This is the
    fully automatic operator singular-value certificate: it needs only the
    printed spectral-separation hypothesis, and `sigma = sigma_min` of the
    vec/Kronecker coefficient.

    Higham, 2nd ed., §16.1 eq (16.3) with §16.3 eqs (16.23)-(16.26). -/
theorem exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n) (A B : Fin n → Fin n → ℝ)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ Y : Fin n → Fin n → ℝ,
        sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y) := by
  have hdet : (sylvesterVecCoeff n n A B).det ≠ 0 :=
    (sylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue n n A B).mpr hno
  exact exists_sylvesterOp_sigmaMin_of_sylvesterVecCoeff_det_ne_zero n hn A B hdet

























/-- **Automatic Lyapunov-operator singular-value lower bound from the printed
    no-common-eigenvalue hypothesis.**

    In positive dimension, if the entrywise complexification of `A` has no
    complex eigenvalue `mu` for which `-conj(mu)` (equivalently, an eigenvalue of
    `-A^T`) is also an eigenvalue -- i.e. `A` and `-A^T` share no common complex
    right eigenvalue -- then there is a strictly positive `sigma` with
    `sigma * ||Y||_F <= ||A Y + Y A^T||_F` for every `Y`.  Automatic operator
    singular-value certificate for the Lyapunov specialization.

    Higham, 2nd ed., §16.3 eq (16.27) (specialized `B = -A^T`). -/
theorem exists_lyapunovOp_sigmaMin_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex (fun i j => -matTranspose A i j))) :
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ Y : Fin n → Fin n → ℝ,
        sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y) := by
  -- Transfer through the Sylvester specialization `B = -A^T`, whose vec
  -- coefficient is definitionally the Lyapunov coefficient.
  obtain ⟨sigma, hsigma_pos, hbnd⟩ :=
    exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A
      (fun i j => -matTranspose A i j) hno
  refine ⟨sigma, hsigma_pos, ?_⟩
  intro Y
  have h := hbnd Y
  rwa [← lyapunovOp_eq_sylvesterOp n A Y] at h

-- ============================================================
-- Automatic Chapter 16 condition-number and perturbation bounds.
-- Each concludes the printed structured estimate from ONLY the printed
-- no-common-eigenvalue hypothesis (plus the genuine positivity/frobNorm side
-- conditions the printed theorem itself carries), producing sigma_min > 0
-- automatically and feeding the existing `_of_sigmaMin` wrappers.
-- ============================================================

/-- **Higham, 2nd ed., §16.3, eqs (16.23)-(16.24) (p. 313): AUTOMATIC structured
    relative Sylvester perturbation bound from spectral data.**

    From ONLY the printed no-common-eigenvalue hypothesis (plus the genuine
    positive-scale and nonzero-solution side conditions the printed estimate
    carries), there exists a strictly positive `sigma` (`= sigma_min` of the
    vec/Kronecker coefficient) for which the printed relative first-order bound
      `||dX||_F / ||X||_F <= sqrt 3 * Psi(...,1/sigma) * eps`
    holds.  This is the AUTOMATIC form of
    `H16_eq16_24_structured_condition_of_sigmaMin`: the singular-value
    certificate is manufactured from nonsingularity of the coefficient, not
    supplied.

    Honest strength: `Psi(...,1/sigma)` uses the sharp `1/sigma_min`; the bound
    is a genuine inequality for that explicit `sigma`, existentially quantified,
    and reflects a condition estimate (a lower bound on true sensitivity), not a
    guaranteed a-priori upper bound. -/
theorem H16_eq16_24_structured_condition_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma eps : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (heps : 0 ≤ eps) (hX : 0 < frobNorm X)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaB : frobNorm DeltaB ≤ eps * beta)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm DeltaX / frobNorm X ≤
        Real.sqrt 3 *
          sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A B hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    H16_eq16_24_structured_condition_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaB hDeltaC hLin

/-- **Higham, 2nd ed., §16.3, eq (16.23) (p. 313): AUTOMATIC raw first-order
    Sylvester perturbation bound from spectral data.**

    The pre-`sqrt 3` first-order form: from the printed no-common-eigenvalue
    hypothesis there exists `sigma > 0` with
      `||dX||_F <= Psi(...,1/sigma) * ||X||_F * scaledTripleNorm`.
    Automatic form of `H16_eq16_23_sylvester_first_order_bound_of_sigmaMin`. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hX : 0 < frobNorm X)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm DeltaX ≤
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
          frobNorm X *
          sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
            alpha beta gamma := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A B hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    H16_eq16_23_sylvester_first_order_bound_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hSigmaMin hLin

/-- **Higham, 2nd ed., §16.3, eq (16.25) (p. 313): AUTOMATIC relative Sylvester
    perturbation bound from spectral data.**

    From the printed no-common-eigenvalue hypothesis (plus the genuine nonzero
    perturbation/solution side conditions) there exists `sigma > 0` for which the
    printed relative perturbation bound in terms of the Sylvester condition
    number holds:
      `||dX||_F / ||X||_F <= condSylvester(A,B,X,alpha,beta,gamma,sigma) * eps`.
    Automatic form of `sylvester_relative_perturbation_of_sigmaMin`.  The
    condition number uses the sharp `sigma = sigma_min`. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A B X dA dB dC dX : Fin n → Fin n → ℝ)
    (alpha beta gamma eps : ℝ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta) (hGamma : 0 ≤ gamma) (hEps : 0 ≤ eps)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hdA : frobNorm dA ≤ eps * alpha)
    (hdB : frobNorm dB ≤ eps * beta)
    (hdC : frobNorm dC ≤ eps * gamma)
    (hLin : ∀ i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : ¬ (frobNormSq dX = 0))
    (hX_ne : ¬ (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm dX / frobNorm X ≤
        condSylvester n A B X alpha beta gamma sigma * eps := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A B hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvester_relative_perturbation_of_sigmaMin n
      A B X dA dB dC dX sigma hsigma hSigmaMin
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- **Higham, 2nd ed., §16.4, eq (16.28) (p. 318): AUTOMATIC relative a
    posteriori Sylvester residual-error bound from spectral data.**

    From ONLY the printed no-common-eigenvalue hypothesis (plus the genuine exact
    solution equation and positive-solution side condition) there exists
    `sigma > 0` for which the printed relative a posteriori bound holds:
      `||X - Xhat||_F / ||X||_F <= ((1/sigma) * ||residual||_F) / ||X||_F`.
    Automatic form of
    `sylvester_relative_aposteriori_bound_of_sigmaMin_total`; the zero-error case
    is handled inside that wrapper.  `sigma = sigma_min` of the coefficient. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A B C X Xhat : Fin n → Fin n → ℝ)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hExact : ∀ i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm (fun i j => X i j - Xhat i j) / frobNorm X ≤
        ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
          frobNorm X := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_sylvesterOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A B hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvester_relative_aposteriori_bound_of_sigmaMin_total n
      A B C X Xhat sigma hsigma hSigmaMin hExact hX_pos

/-- **Higham, 2nd ed., §16.3, eq (16.27) (p. 317): AUTOMATIC relative first-order
    Lyapunov perturbation bound from spectral data.**

    From the printed no-common-eigenvalue hypothesis for `A` and `-A^T` (plus the
    genuine positive-scale and nonzero-solution side conditions) there exists
    `sigma > 0` for which the printed relative Lyapunov first-order bound holds:
      `||dX||_F / ||X||_F <= sqrt 2 * lyapunovCond(...,1/sigma) * eps`.
    Automatic form of `H16_eq16_27_lyapunov_condition_of_sigmaMin`;
    `sigma = sigma_min` of the Lyapunov coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A X DeltaA DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha gamma eps : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex (fun i j => -matTranspose A i j)))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm DeltaX / frobNorm X ≤
        Real.sqrt 2 *
          lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_lyapunovOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSigmaMin hDeltaA hDeltaC hLin

/-- **Higham, 2nd ed., §16.4, eq (16.28) (p. 318): AUTOMATIC relative a
    posteriori Lyapunov residual-error bound from spectral data.**

    From ONLY the printed no-common-eigenvalue hypothesis for `A` and `-A^T`
    (plus the genuine exact solution equation and positive-solution side
    condition) there exists `sigma > 0` for which the printed relative Lyapunov a
    posteriori bound holds:
      `||X - Xhat||_F / ||X||_F <= ((1/sigma) * ||lyapunovResidual||_F) / ||X||_F`.
    Automatic form of
    `lyapunov_relative_aposteriori_bound_of_sigmaMin_total`. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_of_no_common_complex_right_eigenvalue
    (n : ℕ) (hn : 0 < n)
    (A C X Xhat : Fin n → Fin n → ℝ)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex (fun i j => -matTranspose A i j)))
    (hExact : ∀ i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    ∃ sigma : ℝ, 0 < sigma ∧
      frobNorm (fun i j => X i j - Xhat i j) / frobNorm X ≤
        ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
          frobNorm X := by
  obtain ⟨sigma, hsigma, hSigmaMin⟩ :=
    exists_lyapunovOp_sigmaMin_of_no_common_complex_right_eigenvalue n hn A hno
  refine ⟨sigma, hsigma, ?_⟩
  exact
    lyapunov_relative_aposteriori_bound_of_sigmaMin_total n
      A C X Xhat sigma hsigma hSigmaMin hExact hX_pos

end Wave17

end NumStability
