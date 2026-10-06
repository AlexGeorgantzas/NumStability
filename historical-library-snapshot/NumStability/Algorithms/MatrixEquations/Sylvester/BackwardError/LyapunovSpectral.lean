import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.Specification
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.SylvesterSVD
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.BackwardError.LyapunovSpectral

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Algorithms/Sylvester/SylvesterBackward.lean
--
-- SVD-based backward error analysis for the Sylvester equation (Higham §16.2).
-- Eqs 16.13-16.19: backward error characterization via SVD coordinates,
-- lower/upper bounds on η(Y), amplification factor μ, and the Lyapunov
-- scalar-coordinate and xi/mu analogues in §16.2.1.












namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- SVD representation (§16.2, eq 16.13)
-- ============================================================










-- ============================================================
-- Transformed residual in SVD coordinates (§16.2, eq 16.13)
-- ============================================================

















-- ============================================================
-- Backward error ξ² definition (§16.2, eq 16.16)
-- ============================================================










































-- ============================================================
-- Backward error lower bound (§16.2, eq 16.15 lower)
-- ============================================================























































-- ============================================================
-- Backward error upper bound (§16.2, eq 16.15 upper)
-- ============================================================


















































































































































































































































































-- ============================================================
-- Amplification factor (§16.2, eqs 16.17-16.19)
-- ============================================================






































































































































































































-- ============================================================
-- Backward error η bound via cost (§16.2)
-- ============================================================







































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Residual-based backward error bound (combining eqs 16.12 + 16.16)
-- ============================================================



















-- ============================================================
-- Lyapunov spectral-coordinate backward error (§16.2.1, eq 16.21)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    spectral-coordinate transform `U^T M U` used for the Lyapunov residual and
    perturbations. -/
noncomputable def lyapunovSpectralTransform (n : ℕ)
    (U M : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (matTranspose U) M) U

/-- Orthogonal spectral coordinates preserve the squared Frobenius norm. -/
theorem lyapunovSpectralTransform_frobNormSq (n : ℕ)
    (U M : Fin n → Fin n → ℝ) (hU : IsOrthogonal n U) :
    frobNormSq (lyapunovSpectralTransform n U M) = frobNormSq M := by
  unfold lyapunovSpectralTransform
  rw [frobNormSq_orthogonal_right _ _ hU, frobNormSq_orthogonal_left _ _ hU.transpose]

/-- The Lyapunov spectral-coordinate transform commutes with transpose. -/
theorem lyapunovSpectralTransform_transpose (n : ℕ)
    (U M : Fin n → Fin n → ℝ) :
    matTranspose (lyapunovSpectralTransform n U M) =
      lyapunovSpectralTransform n U (matTranspose M) := by
  unfold lyapunovSpectralTransform
  rw [matTranspose_matMul]
  rw [matTranspose_matMul]
  rw [matTranspose_involutive]
  exact (matMul_assoc n (matTranspose U) (matTranspose M) U).symm

/-- Symmetry of the right-hand Lyapunov perturbation is preserved after the
    spectral-coordinate transform `U^T M U`. -/
theorem lyapunovSpectralTransform_symmetric (n : ℕ)
    (U M : Fin n → Fin n → ℝ)
    (hM : IsSymmetricFiniteMatrix M) :
    IsSymmetricFiniteMatrix (lyapunovSpectralTransform n U M) := by
  intro i j
  have hMt : matTranspose M = M := by
    ext a b
    exact hM b a
  have hT := lyapunovSpectralTransform_transpose n U M
  rw [hMt] at hT
  simpa [matTranspose] using congrFun (congrFun hT j) i

/-- The Lyapunov action `A * Y + Y * A^T` is symmetric whenever `Y` is
    symmetric. -/
theorem lyapunovOp_symmetric_of_symmetric (n : ℕ)
    (A Y : Fin n → Fin n → ℝ)
    (hY : IsSymmetricFiniteMatrix Y) :
    IsSymmetricFiniteMatrix (lyapunovOp n A Y) := by
  intro i j
  unfold lyapunovOp matMul matTranspose
  have hleft :
      (∑ k : Fin n, A i k * Y k j) =
        ∑ k : Fin n, Y j k * A i k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hY k j]
    ring
  have hright :
      (∑ k : Fin n, Y i k * A j k) =
        ∑ k : Fin n, A j k * Y k i := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hY i k]
    ring
  rw [hleft, hright]
  ring

/-- Higham, 2nd ed., Chapter 16.2.1:
    if the Lyapunov data `C` and approximate solution `Y` are symmetric, then
    the residual `R = C - A * Y - Y * A^T` is symmetric. -/
theorem lyapunovResidual_symmetric_of_symmetric (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ)
    (hC : IsSymmetricFiniteMatrix C) (hY : IsSymmetricFiniteMatrix Y) :
    IsSymmetricFiniteMatrix (lyapunovResidual n A C Y) := by
  intro i j
  unfold lyapunovResidual
  have hOp := lyapunovOp_symmetric_of_symmetric n A Y hY i j
  rw [hC i j, hOp]

/-- The spectral Lyapunov residual `U^T R U` is symmetric when the source
    Lyapunov right-hand side and approximate solution are symmetric. -/
theorem lyapunovSpectralTransform_residual_symmetric_of_symmetric (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ)
    (hC : IsSymmetricFiniteMatrix C) (hY : IsSymmetricFiniteMatrix Y) :
    IsSymmetricFiniteMatrix
      (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)) :=
  lyapunovSpectralTransform_symmetric n U (lyapunovResidual n A C Y)
    (lyapunovResidual_symmetric_of_symmetric n A C Y hC hY)

/-- Spectral-coordinate transforms distribute over the `M + N - P` matrix
    combination used in the Lyapunov perturbation residual. -/
theorem lyapunovSpectralTransform_add_sub (n : ℕ)
    (U M N P : Fin n → Fin n → ℝ) :
    lyapunovSpectralTransform n U (fun i j => M i j + N i j - P i j) =
      fun i j => lyapunovSpectralTransform n U M i j +
        lyapunovSpectralTransform n U N i j -
          lyapunovSpectralTransform n U P i j := by
  ext i j
  unfold lyapunovSpectralTransform matMul matTranspose
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_add, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Higham, 2nd ed., Chapter 16.2.1:
    original-coordinate Lyapunov perturbation residual
    `DeltaA * Y + Y * DeltaA^T - DeltaC`. -/
noncomputable def lyapunovBackwardResidual (n : ℕ)
    (DA DC Y : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n DA Y i j + matMul n Y (matTranspose DA) i j - DC i j







/-- Higham, 2nd ed., Chapter 16.2.1:
    nonnegative feasible values for the structured Lyapunov backward error
    `eta(Y)`, with a tied `DeltaA`/`DeltaA^T` perturbation and symmetric
    `DeltaC`. -/
def lyapunovBackwardErrorValues (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real) : Set Real :=
  {eta | 0 <= eta ∧ IsLyapunovBackwardError n A C Y alpha gamma eta}

/-- Higham, 2nd ed., Chapter 16.2.1:
    structured Lyapunov `eta(Y)` modeled as the infimum of nonnegative feasible
    structured certificates.  This records the source's Lyapunov-specific
    feasible set separately from the general Sylvester eta model. -/
noncomputable def lyapunovBackwardErrorInf (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real) : Real :=
  sInf (lyapunovBackwardErrorValues n A C Y alpha gamma)











/-- The nonnegative feasible-value set for the structured Lyapunov eta model
    is bounded below by zero. -/
theorem lyapunovBackwardErrorValues_bddBelow (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real) :
    BddBelow (lyapunovBackwardErrorValues n A C Y alpha gamma) := by
  refine ⟨0, ?_⟩
  intro eta heta
  exact heta.1

/-- The structured Lyapunov eta infimum is nonnegative because all feasible
    values are explicitly nonnegative. -/
theorem lyapunovBackwardErrorInf_nonneg (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real) :
    0 <= lyapunovBackwardErrorInf n A C Y alpha gamma := by
  unfold lyapunovBackwardErrorInf lyapunovBackwardErrorValues
  apply Real.sInf_nonneg
  intro eta heta
  exact heta.1

/-- Any nonnegative structured Lyapunov backward-error certificate lies above
    the structured Lyapunov eta infimum. -/
theorem lyapunovBackwardErrorInf_le_of_backwardError (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma eta : Real)
    (heta_nonneg : 0 <= eta)
    (hBack : IsLyapunovBackwardError n A C Y alpha gamma eta) :
    lyapunovBackwardErrorInf n A C Y alpha gamma <= eta := by
  unfold lyapunovBackwardErrorInf
  exact csInf_le
    (lyapunovBackwardErrorValues_bddBelow n A C Y alpha gamma)
    ⟨heta_nonneg, hBack⟩












/-- Higham, 2nd ed., Chapter 16.2.1:
    from the perturbed Lyapunov equation, the residual decomposes as
    `R = DeltaA * Y + Y * DeltaA^T - DeltaC`. -/
theorem lyapunovResidual_decomposition (n : Nat)
    (A C Y DeltaA DeltaC : Fin n -> Fin n -> Real)
    (hEq : ∀ i j, lyapunovOp n (fun i' j' => A i' j' + DeltaA i' j') Y i j =
      C i j + DeltaC i j) :
    lyapunovResidual n A C Y =
      lyapunovBackwardResidual n DeltaA DeltaC Y := by
  ext i j
  have h := hEq i j
  unfold lyapunovOp at h
  unfold lyapunovResidual lyapunovOp lyapunovBackwardResidual
  unfold matMul matTranspose at h ⊢
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at h
  linarith

/-- Higham, 2nd ed., Chapter 16.2.1:
    a Lyapunov perturbation residual equality gives the perturbed Lyapunov
    backward-error equation. -/
theorem lyapunovBackwardError_equation_of_backwardResidual_eq (n : Nat)
    (A C Y DA DC : Fin n -> Fin n -> Real)
    (hResidual : lyapunovBackwardResidual n DA DC Y = lyapunovResidual n A C Y) :
    ∀ i j : Fin n,
      lyapunovOp n (fun i' j' => A i' j' + DA i' j') Y i j =
        C i j + DC i j := by
  intro i j
  have h := congrFun (congrFun hResidual i) j
  unfold lyapunovBackwardResidual lyapunovResidual lyapunovOp matMul matTranspose at h
  unfold lyapunovOp matMul matTranspose
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at h ⊢
  linarith

/-- A Lyapunov perturbation residual is the Sylvester perturbation residual
    with the tied choice `DeltaB = -DeltaA^T`. -/
theorem lyapunovBackwardResidual_eq_sylvesterBackwardResidual_tied (n : Nat)
    (DeltaA DeltaC Y : Fin n -> Fin n -> Real) :
    lyapunovBackwardResidual n DeltaA DeltaC Y =
      sylvesterBackwardResidual n DeltaA
        (fun i j => -matTranspose DeltaA i j) DeltaC Y := by
  ext i j
  unfold lyapunovBackwardResidual sylvesterBackwardResidual matMul matTranspose
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- Higham, 2nd ed., Chapter 16.2.1:
    every structured Lyapunov backward-error certificate is a general
    Sylvester backward-error certificate for the specialization
    `B = -A^T`, with the tied perturbation `DeltaB = -DeltaA^T`. -/
theorem isBackwardError_of_isLyapunovBackwardError (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma eta : Real)
    (hLyap : IsLyapunovBackwardError n A C Y alpha gamma eta) :
    IsBackwardError n A (fun i j => -matTranspose A i j) C Y
      alpha alpha gamma eta := by
  rcases hLyap with ⟨DeltaA, DeltaC, _hDeltaC_sym, hEq, hDeltaA, hDeltaC⟩
  refine ⟨DeltaA, (fun i j => -matTranspose DeltaA i j), DeltaC, ?_, hDeltaA, ?_, hDeltaC⟩
  · intro i j
    have h := hEq i j
    unfold lyapunovOp at h
    unfold sylvesterOp
    unfold matMul matTranspose at h ⊢
    simp only [add_mul, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib] at h ⊢
    linarith
  · calc
      frobNormSq (fun i j : Fin n => -matTranspose DeltaA i j)
          = frobNormSq (matTranspose DeltaA) := by
            simpa using frobNormSq_neg (matTranspose DeltaA)
      _ = frobNormSq DeltaA := frobNormSq_transpose DeltaA
      _ <= (eta * alpha) ^ 2 := hDeltaA

/-- A structured Lyapunov feasible value is also feasible for the relaxed
    general Sylvester eta model with `B = -A^T` and equal `A`/`B` weights. -/
theorem sylvesterBackwardErrorValues_of_lyapunovBackwardErrorValues (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma eta : Real)
    (heta : eta ∈ lyapunovBackwardErrorValues n A C Y alpha gamma) :
    eta ∈ sylvesterBackwardErrorValues n A
      (fun i j => -matTranspose A i j) C Y alpha alpha gamma := by
  exact ⟨heta.1,
    isBackwardError_of_isLyapunovBackwardError n A C Y alpha gamma eta heta.2⟩

/-- Since the structured Lyapunov feasible set is a subset of the relaxed
    Sylvester feasible set, the relaxed Sylvester eta infimum is no larger than
    the structured Lyapunov eta infimum whenever the structured set is nonempty. -/
theorem sylvesterBackwardErrorInf_le_lyapunovBackwardErrorInf (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real)
    (hne : (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty) :
    sylvesterBackwardErrorInf n A (fun i j => -matTranspose A i j) C Y
      alpha alpha gamma <=
        lyapunovBackwardErrorInf n A C Y alpha gamma := by
  unfold lyapunovBackwardErrorInf
  apply le_csInf hne
  intro eta heta
  exact sylvesterBackwardErrorInf_le_of_backwardError n A
    (fun i j => -matTranspose A i j) C Y alpha alpha gamma eta
    heta.1
    (isBackwardError_of_isLyapunovBackwardError n A C Y alpha gamma eta heta.2)

/-- The Lyapunov residual is the Sylvester residual for the specialization
    `B = -A^T`. -/
theorem lyapunovResidual_eq_sylvesterResidual_special (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) :
    lyapunovResidual n A C Y =
      sylvesterResidual n A (fun i j => -matTranspose A i j) C Y := by
  ext i j
  unfold lyapunovResidual sylvesterResidual
  rw [lyapunovOp_eq_sylvesterOp]

/-- Higham, 2nd ed., Chapter 16.2.1:
    a structured Lyapunov backward-error certificate at cost `eta` gives the
    Lyapunov residual bound with the tied-perturbation scale
    `(2 * alpha * ||Y||_F + gamma) * eta`. -/
theorem lyapunov_residual_bound_of_backward_error (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma eta : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heta : 0 <= eta)
    (hLyap : IsLyapunovBackwardError n A C Y alpha gamma eta) :
    frobNorm (lyapunovResidual n A C Y) <=
      (2 * alpha * frobNorm Y + gamma) * eta := by
  rcases isBackwardError_of_isLyapunovBackwardError n A C Y alpha gamma eta hLyap with
    ⟨DeltaA, DeltaB, DeltaC, hEq, hDeltaA_sq, hDeltaB_sq, hDeltaC_sq⟩
  have hDeltaA :
      frobNorm DeltaA <= eta * alpha :=
    frobNorm_le_of_frobNormSq_le_sq DeltaA
      (mul_nonneg heta halpha) hDeltaA_sq
  have hDeltaB :
      frobNorm DeltaB <= eta * alpha :=
    frobNorm_le_of_frobNormSq_le_sq DeltaB
      (mul_nonneg heta halpha) hDeltaB_sq
  have hDeltaC :
      frobNorm DeltaC <= eta * gamma :=
    frobNorm_le_of_frobNormSq_le_sq DeltaC
      (mul_nonneg heta hgamma) hDeltaC_sq
  have hres :=
    residual_bound n A (fun i j => -matTranspose A i j) C Y
      DeltaA DeltaB DeltaC alpha alpha gamma eta
      halpha halpha hgamma heta hEq hDeltaA hDeltaB hDeltaC
  calc
    frobNorm (lyapunovResidual n A C Y)
        = frobNorm (sylvesterResidual n A
            (fun i j => -matTranspose A i j) C Y) := by
            rw [lyapunovResidual_eq_sylvesterResidual_special]
    _ <= ((alpha + alpha) * frobNorm Y + gamma) * eta := hres
    _ = (2 * alpha * frobNorm Y + gamma) * eta := by ring

/-- Higham, 2nd ed., Chapter 16.2.1:
    the residual ratio with Lyapunov scale `2 * alpha * ||Y||_F + gamma`
    is a lower bound for the structured Lyapunov backward-error infimum. -/
theorem lyapunov_relative_residual_le_backwardErrorInf (n : Nat)
    (A C Y : Fin n -> Fin n -> Real) (alpha gamma : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma)
    (hscale : 0 < 2 * alpha * frobNorm Y + gamma)
    (hne : (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty) :
    frobNorm (lyapunovResidual n A C Y) /
        (2 * alpha * frobNorm Y + gamma) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma := by
  unfold lyapunovBackwardErrorInf
  apply le_csInf hne
  intro eta heta
  have hbound :=
    lyapunov_residual_bound_of_backward_error n A C Y alpha gamma eta
      halpha hgamma heta.1 heta.2
  rw [div_le_iff₀ hscale]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound













/-- If `Y = U * Lambda * U^T`, the left perturbation product transforms to
    `DeltaA_tilde * Lambda`. -/
theorem lyapunovSpectralTransform_mul_spectral_right (n : ℕ)
    (U DA : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (matMul n DA (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))) =
        matMul n (lyapunovSpectralTransform n U DA) (diagMatrix lam) := by
  unfold lyapunovSpectralTransform
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  simp [matMul_assoc, hUtU, matMul_id_right]

/-- If `Y = U * Lambda * U^T`, the right perturbation product transforms to
    `Lambda * DeltaA_tilde^T`. -/
theorem lyapunovSpectralTransform_spectral_left_transpose (n : ℕ)
    (U DA : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
        (matTranspose DA)) =
        matMul n (diagMatrix lam)
          (matTranspose (lyapunovSpectralTransform n U DA)) := by
  unfold lyapunovSpectralTransform
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  calc
    matMul n (matMul n (matTranspose U)
        (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
          (matTranspose DA))) U
        = matMul n (matMul n (matMul n (matTranspose U) U)
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA))) U := by
            rw [matMul_assoc n U (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA)]
            rw [(matMul_assoc n (matTranspose U) U
              (matMul n (matMul n (diagMatrix lam) (matTranspose U))
                (matTranspose DA))).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA))) U := by
            rw [hUtU]
    _ = matMul n
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA)) U := by
            rw [matMul_id_left]
    _ = matMul n (diagMatrix lam)
            (matMul n (matTranspose U) (matMul n (matTranspose DA) U)) := by
            rw [matMul_assoc n (diagMatrix lam) (matTranspose U) (matTranspose DA)]
            rw [matMul_assoc n (diagMatrix lam)
              (matMul n (matTranspose U) (matTranspose DA)) U]
            rw [matMul_assoc n (matTranspose U) (matTranspose DA) U]
    _ = matMul n (diagMatrix lam)
            (matTranspose (matMul n (matMul n (matTranspose U) DA) U)) := by
            rw [matTranspose_matMul]
            rw [matTranspose_matMul]
            rw [matTranspose_involutive]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the transformed Lyapunov backward-error residual
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`, written
    entrywise in the diagonal spectral coordinates of the symmetric approximate
    solution. -/
noncomputable def lyapunovSpectralBackwardResidual (n : ℕ)
    (DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => DA i j * lam j + lam i * DA j i - DC i j

/-- The entrywise residual from equation (16.21) is the diagonal-matrix
    expression `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`. -/
theorem lyapunovSpectralBackwardResidual_eq_diagMatrix (n : ℕ)
    (DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    lyapunovSpectralBackwardResidual n DA DC lam =
      fun i j =>
        matMul n DA (diagMatrix lam) i j +
          matMul n (diagMatrix lam) (matTranspose DA) i j -
            DC i j := by
  ext i j
  unfold lyapunovSpectralBackwardResidual
  rw [matMul_diagMatrix_right DA lam i j,
    matMul_diagMatrix_left lam (matTranspose DA) i j]
  simp [matTranspose]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    transforming the original-coordinate Lyapunov perturbation residual with
    `Y = U * Lambda * U^T` gives the diagonal spectral-coordinate residual
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`. -/
theorem lyapunovSpectralTransform_backwardResidual (n : ℕ)
    (U DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (lyapunovBackwardResidual n DA DC
        (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))) =
      lyapunovSpectralBackwardResidual n
        (lyapunovSpectralTransform n U DA)
        (lyapunovSpectralTransform n U DC) lam := by
  unfold lyapunovBackwardResidual
  rw [lyapunovSpectralTransform_add_sub n U
    (matMul n DA (matMul n U (matMul n (diagMatrix lam) (matTranspose U))))
    (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
      (matTranspose DA))
    DC]
  rw [lyapunovSpectralTransform_mul_spectral_right n U DA lam hU]
  rw [lyapunovSpectralTransform_spectral_left_transpose n U DA lam hU]
  rw [lyapunovSpectralBackwardResidual_eq_diagMatrix n
    (lyapunovSpectralTransform n U DA) (lyapunovSpectralTransform n U DC) lam]

/-- Symmetry of the transformed Lyapunov right-hand perturbation is preserved
    by the original-coordinate lift `U * DeltaC_tilde * U^T`. -/
theorem lyapunovLiftDeltaC_symmetric (n : ℕ)
    (U DC_tilde : Fin n → Fin n → ℝ)
    (hDC : IsSymmetricFiniteMatrix DC_tilde) :
    IsSymmetricFiniteMatrix (svdLiftDeltaC n U U DC_tilde) := by
  have h := lyapunovSpectralTransform_symmetric n (matTranspose U) DC_tilde hDC
  simpa [lyapunovSpectralTransform, svdLiftDeltaC, matTranspose_involutive,
    matMul_assoc] using h

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    if lifted spectral-coordinate perturbations satisfy the transformed
    Lyapunov residual equation, then their original-coordinate Lyapunov
    backward residual is the supplied original residual. -/
theorem lyapunovLift_backwardResidual_eq (n : ℕ)
    (Y R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (DA_tilde DC_tilde : Fin n → Fin n → ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hEq : ∀ i j : Fin n,
      DA_tilde i j * lam j + lam i * DA_tilde j i - DC_tilde i j =
        lyapunovSpectralTransform n U R i j) :
    lyapunovBackwardResidual n
        (svdLiftDeltaA n U DA_tilde)
        (svdLiftDeltaC n U U DC_tilde) Y = R := by
  subst Y
  let DA : Fin n → Fin n → ℝ := svdLiftDeltaA n U DA_tilde
  let DC : Fin n → Fin n → ℝ := svdLiftDeltaC n U U DC_tilde
  have hcoords :
      lyapunovSpectralTransform n U
          (lyapunovBackwardResidual n DA DC
            (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))) =
        lyapunovSpectralTransform n U R := by
    rw [lyapunovSpectralTransform_backwardResidual n U DA DC lam hU]
    have hDAcoords : lyapunovSpectralTransform n U DA = DA_tilde := by
      dsimp [DA]
      simpa [lyapunovSpectralTransform] using
        svdLiftDeltaA_svd_coordinates n U DA_tilde hU
    have hDCcoords : lyapunovSpectralTransform n U DC = DC_tilde := by
      dsimp [DC]
      simpa [lyapunovSpectralTransform, svdResidual] using
        svdResidual_svdLiftDeltaC n U U DC_tilde hU hU
    rw [hDAcoords, hDCcoords]
    ext i j
    simpa [lyapunovSpectralBackwardResidual] using hEq i j
  calc
    lyapunovBackwardResidual n DA DC
        (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
        = matMul n U (matMul n
            (lyapunovSpectralTransform n U
              (lyapunovBackwardResidual n DA DC
                (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))))
            (matTranspose U)) := by
            simpa [lyapunovSpectralTransform, svdResidual] using
              (svdResidual_inverse n U U
                (lyapunovBackwardResidual n DA DC
                  (matMul n U (matMul n (diagMatrix lam) (matTranspose U))))
                hU hU).symm
    _ = matMul n U (matMul n (lyapunovSpectralTransform n U R) (matTranspose U)) := by
            rw [hcoords]
    _ = R := by
            simpa [lyapunovSpectralTransform, svdResidual] using
              svdResidual_inverse n U U R hU hU

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the printed scaled scalar equation in Lyapunov spectral coordinates. -/
def lyapunovBackwardScalarEq (n : ℕ) (lam : Fin n → ℝ) (α γ : ℝ)
    (DA DC R_tilde : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n,
    (DA i j / α) * (α * lam j) +
      (α * lam i) * (DA j i / α) -
        γ * (DC i j / γ) = R_tilde i j

/-- Equation (16.21) is equivalent to the unscaled transformed residual equation
    when the source scaling parameters are nonzero. -/
theorem lyapunovBackwardScalarEq_iff_unscaled (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      ∀ i j : Fin n, DA i j * lam j + lam i * DA j i - DC i j = R_tilde i j := by
  constructor
  · intro h i j
    have hscale :
        (DA i j / α) * (α * lam j) +
          (α * lam i) * (DA j i / α) -
            γ * (DC i j / γ) =
          DA i j * lam j + lam i * DA j i - DC i j := by
      field_simp [hα, hγ]
    simpa [hscale] using h i j
  · intro h i j
    have hscale :
        (DA i j / α) * (α * lam j) +
          (α * lam i) * (DA j i / α) -
            γ * (DC i j / γ) =
          DA i j * lam j + lam i * DA j i - DC i j := by
      field_simp [hα, hγ]
    rw [hscale]
    exact h i j

/-- Equation (16.21) as an equality between the transformed Lyapunov residual
    matrix and the transformed residual right-hand side. -/
theorem lyapunovBackwardScalarEq_iff_residual_eq (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      lyapunovSpectralBackwardResidual n DA DC lam = R_tilde := by
  rw [lyapunovBackwardScalarEq_iff_unscaled n lam α γ DA DC R_tilde hα hγ]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the printed scaled scalar equation follows from the original residual
    equation after the orthogonal spectral decomposition `Y = U * Lambda * U^T`. -/
theorem lyapunovBackwardScalarEq_of_spectral_decomposition (n : ℕ)
    (U DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hU : IsOrthogonal n U) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ
      (lyapunovSpectralTransform n U DA)
      (lyapunovSpectralTransform n U DC)
      (lyapunovSpectralTransform n U
        (lyapunovBackwardResidual n DA DC
          (matMul n U (matMul n (diagMatrix lam) (matTranspose U))))) := by
  rw [lyapunovBackwardScalarEq_iff_residual_eq n lam α γ
    (lyapunovSpectralTransform n U DA)
    (lyapunovSpectralTransform n U DC)
    (lyapunovSpectralTransform n U
      (lyapunovBackwardResidual n DA DC
        (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))))
    hα hγ]
  exact (lyapunovSpectralTransform_backwardResidual n U DA DC lam hU).symm

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    any structured Lyapunov backward-error certificate for a symmetric
    approximation with spectral decomposition `Y = U * Lambda * U^T` gives the
    printed scalar residual equation in spectral coordinates.  The orthogonal
    change of basis preserves the Frobenius bounds on the two perturbations. -/
theorem lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma eta : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U) (halpha : alpha ≠ 0) (hgamma : gamma ≠ 0)
    (hLyap : IsLyapunovBackwardError n A C Y alpha gamma eta) :
    ∃ DeltaA DeltaC : Fin n → Fin n → ℝ,
      IsSymmetricFiniteMatrix DeltaC ∧
      frobNormSq (lyapunovSpectralTransform n U DeltaA) ≤ (eta * alpha) ^ 2 ∧
      frobNormSq (lyapunovSpectralTransform n U DeltaC) ≤ (eta * gamma) ^ 2 ∧
      lyapunovBackwardScalarEq n lam alpha gamma
        (lyapunovSpectralTransform n U DeltaA)
        (lyapunovSpectralTransform n U DeltaC)
        (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)) := by
  subst Y
  rcases hLyap with ⟨DeltaA, DeltaC, hDeltaC_sym, hEq, hDeltaA, hDeltaC⟩
  refine ⟨DeltaA, DeltaC, hDeltaC_sym, ?_, ?_, ?_⟩
  · simpa [lyapunovSpectralTransform_frobNormSq n U DeltaA hU] using hDeltaA
  · simpa [lyapunovSpectralTransform_frobNormSq n U DeltaC hU] using hDeltaC
  · have hresid := lyapunovResidual_decomposition n A C
      (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
      DeltaA DeltaC hEq
    have hscalar :=
      lyapunovBackwardScalarEq_of_spectral_decomposition n U DeltaA DeltaC lam
        alpha gamma hU halpha hgamma
    simpa [hresid] using hscalar

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the structured certificate-to-scalar bridge with the transformed symmetric
    right-hand perturbation side condition exposed explicitly. -/
theorem lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition_symm
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma eta : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U) (halpha : alpha ≠ 0) (hgamma : gamma ≠ 0)
    (hLyap : IsLyapunovBackwardError n A C Y alpha gamma eta) :
    ∃ DeltaA DeltaC : Fin n → Fin n → ℝ,
      IsSymmetricFiniteMatrix (lyapunovSpectralTransform n U DeltaC) ∧
      frobNormSq (lyapunovSpectralTransform n U DeltaA) ≤ (eta * alpha) ^ 2 ∧
      frobNormSq (lyapunovSpectralTransform n U DeltaC) ≤ (eta * gamma) ^ 2 ∧
      lyapunovBackwardScalarEq n lam alpha gamma
        (lyapunovSpectralTransform n U DeltaA)
        (lyapunovSpectralTransform n U DeltaC)
        (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)) := by
  rcases
    lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition
      n A C Y U lam alpha gamma eta hY hU halpha hgamma hLyap with
    ⟨DeltaA, DeltaC, hDeltaC_sym, hDeltaA, hDeltaC, hscalar⟩
  exact ⟨DeltaA, DeltaC,
    lyapunovSpectralTransform_symmetric n U DeltaC hDeltaC_sym,
    hDeltaA, hDeltaC, hscalar⟩

/-- Equation (16.21) as the diagonal-matrix residual equation
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde = R_tilde`. -/
theorem lyapunovBackwardScalarEq_iff_diagMatrix_eq (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      (fun i j =>
        matMul n DA (diagMatrix lam) i j +
          matMul n (diagMatrix lam) (matTranspose DA) i j -
            DC i j) = R_tilde := by
  rw [lyapunovBackwardScalarEq_iff_residual_eq n lam α γ DA DC R_tilde hα hγ]
  rw [lyapunovSpectralBackwardResidual_eq_diagMatrix n DA DC lam]

/-- Higham, 2nd ed., Chapter 16.2.1, unnumbered formula after equation (16.21):
    Lyapunov-structured squared `xi` functional in spectral coordinates. -/
noncomputable def lyapunovXiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) ^ 2

/-- The simple upper summand appearing after the Lyapunov `xi^2` formula. -/
noncomputable def lyapunovXiSqSimpleBound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (2 * R_tilde i j ^ 2) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    coordinatewise Lyapunov optimizer for the transformed `DeltaA` slot. -/
noncomputable def lyapunovOptimalDeltaA (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    (2 * α ^ 2 * lam j * R_tilde i j) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    coordinatewise Lyapunov optimizer for the transformed symmetric `DeltaC`
    slot. -/
noncomputable def lyapunovOptimalDeltaC (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    -(γ ^ 2 * R_tilde i j) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)

/-- The Lyapunov `xi^2` functional is nonnegative when the displayed
    denominators in (16.21) are positive. -/
theorem lyapunovXiSq_nonneg (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    0 ≤ lyapunovXiSq n R_tilde lam α γ := by
  unfold lyapunovXiSq
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (by positivity) (le_of_lt (sq_pos_of_pos (hpos i j)))

/-- For symmetric transformed residuals, the coordinatewise Lyapunov optimizer
    solves the unscaled residual equation underlying (16.21). -/
theorem lyapunovOptimalPerturbations_scalar_eq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hR : IsSymmetricFiniteMatrix R_tilde)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    ∀ i j : Fin n,
      lyapunovOptimalDeltaA n R_tilde lam α γ i j * lam j +
        lam i * lyapunovOptimalDeltaA n R_tilde lam α γ j i -
          lyapunovOptimalDeltaC n R_tilde lam α γ i j =
        R_tilde i j := by
  intro i j
  let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
  have hDen_ne : 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 ≠ 0 :=
    ne_of_gt (hpos i j)
  have hDsym :
      2 * α ^ 2 * (lam j ^ 2 + lam i ^ 2) + γ ^ 2 = D := by
    dsimp [D]
    ring
  have hRji : R_tilde j i = R_tilde i j := hR j i
  unfold lyapunovOptimalDeltaA lyapunovOptimalDeltaC
  rw [hRji, hDsym]
  dsimp [D]
  field_simp [hDen_ne]
  ring

/-- For symmetric transformed residuals, the coordinatewise optimal right-hand
    perturbation in (16.21) is symmetric. -/
theorem lyapunovOptimalDeltaC_symmetric (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hR : IsSymmetricFiniteMatrix R_tilde) :
    IsSymmetricFiniteMatrix (lyapunovOptimalDeltaC n R_tilde lam α γ) := by
  intro i j
  unfold lyapunovOptimalDeltaC
  rw [hR i j]
  ring

/-- The transformed `DeltaA` component of the Lyapunov coordinatewise optimizer
    has squared Frobenius norm bounded by `alpha^2 * xi^2`. -/
theorem lyapunovOptimalDeltaA_frobNormSq_le_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    frobNormSq (lyapunovOptimalDeltaA n R_tilde lam α γ) ≤
      α ^ 2 * lyapunovXiSq n R_tilde lam α γ := by
  unfold frobNormSq lyapunovXiSq lyapunovOptimalDeltaA
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
  have hD_pos : 0 < D := by
    dsimp [D]
    exact hpos i j
  have hD_sq_nonneg : 0 ≤ D ^ 2 := sq_nonneg D
  have hkey :
      (2 * α ^ 2 * lam j * R_tilde i j) ^ 2 ≤
        α ^ 2 * ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) := by
    nlinarith [sq_nonneg (α * γ * R_tilde i j)]
  calc
    ((2 * α ^ 2 * lam j * R_tilde i j) / D) ^ 2
        = (2 * α ^ 2 * lam j * R_tilde i j) ^ 2 / D ^ 2 := by
          rw [div_pow]
    _ ≤ (α ^ 2 * ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) *
          R_tilde i j ^ 2)) / D ^ 2 := by
          exact div_le_div_of_nonneg_right hkey hD_sq_nonneg
    _ = α ^ 2 *
          (((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) *
            R_tilde i j ^ 2) / D ^ 2) := by
          ring

/-- The transformed symmetric `DeltaC` component of the Lyapunov coordinatewise
    optimizer has squared Frobenius norm bounded by `gamma^2 * xi^2`. -/
theorem lyapunovOptimalDeltaC_frobNormSq_le_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    frobNormSq (lyapunovOptimalDeltaC n R_tilde lam α γ) ≤
      γ ^ 2 * lyapunovXiSq n R_tilde lam α γ := by
  unfold frobNormSq lyapunovXiSq lyapunovOptimalDeltaC
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
  have hD_pos : 0 < D := by
    dsimp [D]
    exact hpos i j
  have hD_sq_nonneg : 0 ≤ D ^ 2 := sq_nonneg D
  have hkey :
      (γ ^ 2 * R_tilde i j) ^ 2 ≤
        γ ^ 2 * ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) := by
    nlinarith [sq_nonneg (2 * α * γ * lam j * R_tilde i j)]
  calc
    (-(γ ^ 2 * R_tilde i j) / D) ^ 2
        = (γ ^ 2 * R_tilde i j / D) ^ 2 := by
          ring
    _ = (γ ^ 2 * R_tilde i j) ^ 2 / D ^ 2 := by
          rw [div_pow]
    _ ≤ (γ ^ 2 * ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) *
          R_tilde i j ^ 2)) / D ^ 2 := by
          exact div_le_div_of_nonneg_right hkey hD_sq_nonneg
    _ = γ ^ 2 *
          (((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) *
            R_tilde i j ^ 2) / D ^ 2) := by
          ring

/-- Existence form of the Lyapunov coordinatewise optimizer in spectral
    coordinates: for a symmetric transformed residual, there are transformed
    perturbations solving (16.21), with symmetric `DeltaC` and component
    squared-Frobenius bounds controlled by `xi^2`. -/
theorem exists_lyapunovOptimalPerturbations (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hR : IsSymmetricFiniteMatrix R_tilde)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    ∃ DA DC : Fin n → Fin n → ℝ,
      IsSymmetricFiniteMatrix DC ∧
      (∀ i j : Fin n, DA i j * lam j + lam i * DA j i - DC i j =
        R_tilde i j) ∧
      frobNormSq DA ≤ α ^ 2 * lyapunovXiSq n R_tilde lam α γ ∧
      frobNormSq DC ≤ γ ^ 2 * lyapunovXiSq n R_tilde lam α γ := by
  refine ⟨lyapunovOptimalDeltaA n R_tilde lam α γ,
    lyapunovOptimalDeltaC n R_tilde lam α γ, ?_, ?_, ?_, ?_⟩
  · exact lyapunovOptimalDeltaC_symmetric n R_tilde lam α γ hR
  · exact lyapunovOptimalPerturbations_scalar_eq n R_tilde lam α γ hR hpos
  · exact lyapunovOptimalDeltaA_frobNormSq_le_xiSq n R_tilde lam α γ hpos
  · exact lyapunovOptimalDeltaC_frobNormSq_le_xiSq n R_tilde lam α γ hpos

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), upper direction:
    the coordinatewise Lyapunov optimizer in spectral coordinates lifts to an
    original-coordinate structured Lyapunov backward-error certificate with
    cost `sqrt (xi^2)`. -/
theorem isLyapunovBackwardError_sqrt_lyapunovXiSq_of_spectral_optimalPerturbations
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hR : IsSymmetricFiniteMatrix
      (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)))
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    IsLyapunovBackwardError n A C Y alpha gamma
      (Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma)) := by
  let R_tilde : Fin n → Fin n → ℝ :=
    lyapunovSpectralTransform n U (lyapunovResidual n A C Y)
  let eta : ℝ := Real.sqrt (lyapunovXiSq n R_tilde lam alpha gamma)
  change IsLyapunovBackwardError n A C Y alpha gamma eta
  let DA_tilde : Fin n → Fin n → ℝ :=
    lyapunovOptimalDeltaA n R_tilde lam alpha gamma
  let DC_tilde : Fin n → Fin n → ℝ :=
    lyapunovOptimalDeltaC n R_tilde lam alpha gamma
  refine ⟨svdLiftDeltaA n U DA_tilde, svdLiftDeltaC n U U DC_tilde, ?_, ?_, ?_, ?_⟩
  · have hDCtilde_sym : IsSymmetricFiniteMatrix DC_tilde := by
      simpa [DC_tilde, R_tilde] using
        lyapunovOptimalDeltaC_symmetric n R_tilde lam alpha gamma
          (by simpa [R_tilde] using hR)
    exact lyapunovLiftDeltaC_symmetric n U DC_tilde hDCtilde_sym
  · have hscalar :
        ∀ i j : Fin n,
          DA_tilde i j * lam j + lam i * DA_tilde j i - DC_tilde i j =
            R_tilde i j := by
      simpa [DA_tilde, DC_tilde, R_tilde] using
        lyapunovOptimalPerturbations_scalar_eq n R_tilde lam alpha gamma
          (by simpa [R_tilde] using hR) hpos
    have hResidual :
        lyapunovBackwardResidual n
            (svdLiftDeltaA n U DA_tilde)
            (svdLiftDeltaC n U U DC_tilde) Y =
          lyapunovResidual n A C Y := by
      exact lyapunovLift_backwardResidual_eq n Y (lyapunovResidual n A C Y)
        U lam DA_tilde DC_tilde hY hU
        (by
          intro i j
          simpa [R_tilde] using hscalar i j)
    exact lyapunovBackwardError_equation_of_backwardResidual_eq n A C Y
      (svdLiftDeltaA n U DA_tilde)
      (svdLiftDeltaC n U U DC_tilde) hResidual
  · have hxi : 0 ≤ lyapunovXiSq n R_tilde lam alpha gamma :=
      lyapunovXiSq_nonneg n R_tilde lam alpha gamma hpos
    have hDA := lyapunovOptimalDeltaA_frobNormSq_le_xiSq n R_tilde lam alpha gamma hpos
    rw [svdLiftDeltaA_frobNormSq n U DA_tilde hU]
    calc
      frobNormSq DA_tilde ≤
          alpha ^ 2 * lyapunovXiSq n R_tilde lam alpha gamma := by
          simpa [DA_tilde] using hDA
      _ = (eta * alpha) ^ 2 := by
          unfold eta
          rw [mul_pow, Real.sq_sqrt hxi]
          ring
  · have hxi : 0 ≤ lyapunovXiSq n R_tilde lam alpha gamma :=
      lyapunovXiSq_nonneg n R_tilde lam alpha gamma hpos
    have hDC := lyapunovOptimalDeltaC_frobNormSq_le_xiSq n R_tilde lam alpha gamma hpos
    rw [svdLiftDeltaC_frobNormSq n U U DC_tilde hU hU]
    calc
      frobNormSq DC_tilde ≤
          gamma ^ 2 * lyapunovXiSq n R_tilde lam alpha gamma := by
          simpa [DC_tilde] using hDC
      _ = (eta * gamma) ^ 2 := by
          unfold eta
          rw [mul_pow, Real.sq_sqrt hxi]
          ring

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    for symmetric Lyapunov data with an orthogonal spectral decomposition of
    `Y`, the spectral Lyapunov optimizer gives an original-coordinate
    structured backward-error certificate with cost `sqrt (xi^2)`. -/
theorem isLyapunovBackwardError_sqrt_lyapunovXiSq_of_symmetric_spectral
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    IsLyapunovBackwardError n A C Y alpha gamma
      (Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma)) := by
  exact
    isLyapunovBackwardError_sqrt_lyapunovXiSq_of_spectral_optimalPerturbations
      n A C Y U lam alpha gamma hY hU
      (lyapunovSpectralTransform_residual_symmetric_of_symmetric n A C Y U hC hYsym)
      hpos

/-- The lifted Lyapunov spectral optimizer supplies a nonempty feasible set for
    the infimum model of the structured Lyapunov backward error. -/
theorem lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty := by
  refine ⟨Real.sqrt
      (lyapunovXiSq n
        (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
        lam alpha gamma), ?_⟩
  exact ⟨Real.sqrt_nonneg _,
    isLyapunovBackwardError_sqrt_lyapunovXiSq_of_symmetric_spectral
      n A C Y U lam alpha gamma hY hU hC hYsym hpos⟩

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), upper infimum direction:
    the structured Lyapunov eta infimum is bounded above by the spectral
    optimizer value `sqrt (xi^2)`. -/
theorem lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    lyapunovBackwardErrorInf n A C Y alpha gamma ≤
      Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma) :=
  lyapunovBackwardErrorInf_le_of_backwardError n A C Y alpha gamma
    (Real.sqrt
      (lyapunovXiSq n
        (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
        lam alpha gamma))
    (Real.sqrt_nonneg _)
    (isLyapunovBackwardError_sqrt_lyapunovXiSq_of_symmetric_spectral
      n A C Y U lam alpha gamma hY hU hC hYsym hpos)

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    for a symmetric transformed Lyapunov residual, the asymmetric printed
    `xi^2` summation is exactly half of the subsequent simple residual-weighted
    summation. -/
theorem two_mul_lyapunovXiSq_eq_simple_bound_of_symmetric (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hR : IsSymmetricFiniteMatrix R_tilde)
    (hden : ∀ i j : Fin n,
      2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 ≠ 0) :
    2 * lyapunovXiSq n R_tilde lam α γ =
      lyapunovXiSqSimpleBound n R_tilde lam α γ := by
  unfold lyapunovXiSq lyapunovXiSqSimpleBound
  let term : Fin n → Fin n → ℝ := fun i j =>
    ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) ^ 2
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, term j i) =
        ∑ i : Fin n, ∑ j : Fin n, term i j := by
    rw [Finset.sum_comm]
  have hpair : ∀ i j : Fin n,
      term i j + term j i =
        (2 * R_tilde i j ^ 2) /
          (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) := by
    intro i j
    let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
    have hRji : R_tilde j i = R_tilde i j := hR j i
    have hDsym :
        2 * α ^ 2 * (lam j ^ 2 + lam i ^ 2) + γ ^ 2 =
          D := by
      dsimp [D]
      ring
    have hD_ne : D ≠ 0 := by
      dsimp [D]
      exact hden i j
    have hnum :
        (4 * α ^ 2 * lam j ^ 2 + γ ^ 2) +
            (4 * α ^ 2 * lam i ^ 2 + γ ^ 2) =
          2 * D := by
      dsimp [D]
      ring
    dsimp [term]
    rw [hRji, hDsym]
    change
      ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) / D ^ 2 +
        ((4 * α ^ 2 * lam i ^ 2 + γ ^ 2) * R_tilde i j ^ 2) / D ^ 2 =
          (2 * R_tilde i j ^ 2) / D
    calc
      ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) / D ^ 2 +
          ((4 * α ^ 2 * lam i ^ 2 + γ ^ 2) * R_tilde i j ^ 2) / D ^ 2
          = (((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) +
              (4 * α ^ 2 * lam i ^ 2 + γ ^ 2)) * R_tilde i j ^ 2) /
                D ^ 2 := by
              ring
      _ = (2 * D * R_tilde i j ^ 2) / D ^ 2 := by
            rw [hnum]
      _ = (2 * R_tilde i j ^ 2) / D := by
            field_simp [hD_ne]
  calc
    2 * (∑ i : Fin n, ∑ j : Fin n, term i j)
        = (∑ i : Fin n, ∑ j : Fin n, term i j) +
            (∑ i : Fin n, ∑ j : Fin n, term i j) := by ring
    _ = (∑ i : Fin n, ∑ j : Fin n, term i j) +
          (∑ i : Fin n, ∑ j : Fin n, term j i) := by rw [hswap]
    _ = ∑ i : Fin n, ∑ j : Fin n, (term i j + term j i) := by
          simp [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (2 * R_tilde i j ^ 2) /
            (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hpair i j

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), lower direction:
    each residual term in the simple Lyapunov `xi^2` bound is dominated by the
    normalized structured perturbation cost. -/
theorem lyapunovXiSqSimpleBound_le_scaled_perturbation_cost (n : ℕ)
    (R_tilde DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * lam j + lam i * DA j i - DC i j = R_tilde i j) :
    lyapunovXiSqSimpleBound n R_tilde lam α γ ≤
      ∑ i : Fin n, ∑ j : Fin n,
        (DA i j ^ 2 / α ^ 2 + DA j i ^ 2 / α ^ 2 +
          2 * (DC i j ^ 2 / γ ^ 2)) := by
  unfold lyapunovXiSqSimpleBound
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hD : 0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := hpos i j
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  rw [div_le_iff₀ hD, ← hEq i j]
  rw [show
      DA i j ^ 2 / α ^ 2 + DA j i ^ 2 / α ^ 2 +
          2 * (DC i j ^ 2 / γ ^ 2) =
        (DA i j ^ 2 * γ ^ 2 + DA j i ^ 2 * γ ^ 2 +
            2 * DC i j ^ 2 * α ^ 2) /
          (α ^ 2 * γ ^ 2) from by
        field_simp [hα_ne, hγ_ne]]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity)]
  nlinarith
    [sq_nonneg (α * γ * (lam j * DA j i - lam i * DA i j)),
      sq_nonneg (2 * α ^ 2 * lam j * DC i j + DA i j * γ ^ 2),
      sq_nonneg (2 * α ^ 2 * lam i * DC i j + DA j i * γ ^ 2)]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), lower direction:
    any transformed Lyapunov backward-error certificate bounds the spectral
    `xi^2` functional by `2 * eta^2`. -/
theorem lyapunovXiSq_le_two_eta_sq_of_scalar_eq (n : ℕ)
    (R_tilde DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ η : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (hR : IsSymmetricFiniteMatrix R_tilde)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * lam j + lam i * DA j i - DC i j = R_tilde i j)
    (hDA : frobNormSq DA ≤ (η * α) ^ 2)
    (hDC : frobNormSq DC ≤ (η * γ) ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤ 2 * η ^ 2 := by
  have hcost :=
    lyapunovXiSqSimpleBound_le_scaled_perturbation_cost n R_tilde DA DC lam
      α γ hα hγ hpos hEq
  have hden : ∀ i j : Fin n,
      2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 ≠ 0 := by
    intro i j
    exact ne_of_gt (hpos i j)
  have hpair := two_mul_lyapunovXiSq_eq_simple_bound_of_symmetric
    n R_tilde lam α γ hR hden
  have hα2 : (0 : ℝ) < α ^ 2 := sq_pos_of_pos hα
  have hγ2 : (0 : ℝ) < γ ^ 2 := sq_pos_of_pos hγ
  have hDAbound : frobNormSq DA / α ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hα2]
    nlinarith
  have hDCbound : frobNormSq DC / γ ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hγ2]
    nlinarith
  have hsumDA :
      (∑ i : Fin n, ∑ j : Fin n, DA i j ^ 2 / α ^ 2) ≤ η ^ 2 := by
    simpa [frobNormSq, div_eq_mul_inv, Finset.sum_mul] using hDAbound
  have hsumDA_swap :
      (∑ i : Fin n, ∑ j : Fin n, DA j i ^ 2 / α ^ 2) ≤ η ^ 2 := by
    have hswap :
        (∑ i : Fin n, ∑ j : Fin n, DA j i ^ 2 / α ^ 2) =
          ∑ i : Fin n, ∑ j : Fin n, DA i j ^ 2 / α ^ 2 := by
      rw [Finset.sum_comm]
    rw [hswap]
    exact hsumDA
  have hsumDC_base :
      (∑ i : Fin n, ∑ j : Fin n, DC i j ^ 2 / γ ^ 2) ≤ η ^ 2 := by
    simpa [frobNormSq, div_eq_mul_inv, Finset.sum_mul] using hDCbound
  have hsumDC_eq :
      (∑ i : Fin n, ∑ j : Fin n, 2 * (DC i j ^ 2 / γ ^ 2)) =
        2 * (∑ i : Fin n, ∑ j : Fin n, DC i j ^ 2 / γ ^ 2) := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hsumDC :
      (∑ i : Fin n, ∑ j : Fin n, 2 * (DC i j ^ 2 / γ ^ 2)) ≤ 2 * η ^ 2 := by
    rw [hsumDC_eq]
    exact mul_le_mul_of_nonneg_left hsumDC_base (by norm_num)
  have hsum_split :
      (∑ i : Fin n, ∑ j : Fin n,
        (DA i j ^ 2 / α ^ 2 + DA j i ^ 2 / α ^ 2 +
          2 * (DC i j ^ 2 / γ ^ 2))) =
        (∑ i : Fin n, ∑ j : Fin n, DA i j ^ 2 / α ^ 2) +
          (∑ i : Fin n, ∑ j : Fin n, DA j i ^ 2 / α ^ 2) +
            (∑ i : Fin n, ∑ j : Fin n, 2 * (DC i j ^ 2 / γ ^ 2)) := by
    simp_rw [Finset.sum_add_distrib]
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        (DA i j ^ 2 / α ^ 2 + DA j i ^ 2 / α ^ 2 +
          2 * (DC i j ^ 2 / γ ^ 2))) ≤ 4 * η ^ 2 := by
    rw [hsum_split]
    nlinarith
  have htwice :
      2 * lyapunovXiSq n R_tilde lam α γ ≤ 4 * η ^ 2 := by
    calc
      2 * lyapunovXiSq n R_tilde lam α γ =
          lyapunovXiSqSimpleBound n R_tilde lam α γ := hpair
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (DA i j ^ 2 / α ^ 2 + DA j i ^ 2 / α ^ 2 +
            2 * (DC i j ^ 2 / γ ^ 2)) := hcost
      _ ≤ 4 * η ^ 2 := hsum
  nlinarith

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), lower direction:
    a structured Lyapunov backward-error certificate in original coordinates
    gives the same `xi^2 ≤ 2 * eta^2` bound after orthogonal spectral
    transformation. -/
theorem lyapunovXiSq_le_two_eta_sq_of_backward_error_spectral (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ η : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hLyap : IsLyapunovBackwardError n A C Y α γ η)
    (hα : 0 < α) (hγ : 0 < γ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    lyapunovXiSq n
      (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
      lam α γ ≤ 2 * η ^ 2 := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  rcases
    lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition_symm
      n A C Y U lam α γ η hY hU hα_ne hγ_ne hLyap with
    ⟨DeltaA, DeltaC, _hDeltaC_sym, hDeltaA, hDeltaC, hscalar⟩
  have hR :
      IsSymmetricFiniteMatrix
        (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)) :=
    lyapunovSpectralTransform_residual_symmetric_of_symmetric n A C Y U hC hYsym
  have hEq :
      ∀ i j : Fin n,
        (lyapunovSpectralTransform n U DeltaA) i j * lam j +
          lam i * (lyapunovSpectralTransform n U DeltaA) j i -
            (lyapunovSpectralTransform n U DeltaC) i j =
              (lyapunovSpectralTransform n U (lyapunovResidual n A C Y)) i j :=
    (lyapunovBackwardScalarEq_iff_unscaled n lam α γ
      (lyapunovSpectralTransform n U DeltaA)
      (lyapunovSpectralTransform n U DeltaC)
      (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
      hα_ne hγ_ne).1 hscalar
  exact
    lyapunovXiSq_le_two_eta_sq_of_scalar_eq n
      (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
      (lyapunovSpectralTransform n U DeltaA)
      (lyapunovSpectralTransform n U DeltaC) lam α γ η
      hα hγ hR hpos hEq hDeltaA hDeltaC

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21), lower infimum direction:
    `sqrt (xi^2 / 2)` is a lower bound for all nonnegative structured
    Lyapunov backward-error certificates, hence it is below the infimum model
    of `eta(Y)`. -/
theorem sqrt_lyapunovXiSq_div_two_le_lyapunovBackwardErrorInf_of_symmetric_spectral
    (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hα : 0 < α) (hγ : 0 < γ)
    (hpos : ∀ i j : Fin n,
      0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam α γ / 2) ≤
      lyapunovBackwardErrorInf n A C Y α γ := by
  unfold lyapunovBackwardErrorInf
  apply le_csInf
    (lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral n
      A C Y U lam α γ hY hU hC hYsym hpos)
  intro η hη
  rcases hη with ⟨hη_nonneg, hLyap⟩
  have hle :=
    lyapunovXiSq_le_two_eta_sq_of_backward_error_spectral n
      A C Y U lam α γ η hY hU hC hYsym hLyap hα hγ hpos
  have hdiv :
      lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam α γ / 2 ≤ η ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hη_nonneg] at hsqrt
  exact hsqrt

/-- Higham, 2nd ed., Chapter 16.2.1, unnumbered inequality after equation
    (16.21): the exact Lyapunov `xi^2` summand is bounded by the simpler
    residual-weighted summand when the displayed denominators are positive. -/
theorem lyapunovXiSq_le_simple_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤
      lyapunovXiSqSimpleBound n R_tilde lam α γ := by
  unfold lyapunovXiSq lyapunovXiSqSimpleBound
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
  have hD : 0 < D := hpos i j
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hD_ne : D ≠ 0 := ne_of_gt hD
  have hkey :
      (4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2 ≤
        (2 * R_tilde i j ^ 2) * D := by
    nlinarith [sq_nonneg (R_tilde i j * α * lam i),
      sq_nonneg (R_tilde i j * γ)]
  have hright :
      (2 * R_tilde i j ^ 2 / D) * D ^ 2 =
        (2 * R_tilde i j ^ 2) * D := by
    field_simp [hD_ne]
  rw [div_le_iff₀ hD2]
  rw [hright]
  exact hkey

/-- Higham, 2nd ed., Chapter 16.2.1, final display:
    Lyapunov analogue of the amplification factor `mu`. -/
noncomputable def lyapunovAmplificationMu (α γ yNorm lamStar : ℝ) : ℝ :=
  Real.sqrt 2 * (2 * α * yNorm + γ) /
    Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)

/-- Lyapunov xi-squared residual bound using an explicit lower square bound on
    the simple residual-weighted summation. -/
theorem lyapunovXiSqSimpleBound_le_min_eigen_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSqSimpleBound n R_tilde lam α γ ≤
      2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hdenom_le : ∀ i j : Fin n,
      4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≤
        2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    nlinarith [sq_nonneg α, hLam i, hLam j]
  have hD_ne : 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  unfold lyapunovXiSqSimpleBound
  suffices h :
      (∑ i : Fin n, ∑ j : Fin n,
        (2 * R_tilde i j ^ 2) /
          (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)) ≤
        (∑ i : Fin n, ∑ j : Fin n,
          (2 * R_tilde i j ^ 2) /
            (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) by
    rwa [show
        (∑ i : Fin n, ∑ j : Fin n,
          (2 * R_tilde i j ^ 2) /
            (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) =
          2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) from by
      unfold frobNormSq
      rw [eq_div_iff hD_ne]
      rw [Finset.sum_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact div_mul_cancel₀ _ hD_ne] at h
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact div_le_div_of_nonneg_left (by positivity) hDenom (hdenom_le i j)

/-- Lyapunov xi-squared residual bound using an explicit lower square bound on
    the spectral magnitudes.  This is the xi-level foundation behind the final
    Lyapunov analogue of equations (16.17)-(16.18). -/
theorem lyapunovXiSq_le_min_eigen_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤
      2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hdenom_le : ∀ i j : Fin n,
      4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≤
        2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    nlinarith [sq_nonneg α, hLam i, hLam j]
  have hpos : ∀ i j : Fin n, 0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    exact lt_of_lt_of_le hDenom (hdenom_le i j)
  have hsimple := lyapunovXiSq_le_simple_bound n R_tilde lam α γ hpos
  have hbound :
      lyapunovXiSqSimpleBound n R_tilde lam α γ ≤
        2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
    exact lyapunovXiSqSimpleBound_le_min_eigen_bound n R_tilde lam α γ lamStar
      hLam hDenom
  exact le_trans hsimple hbound

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    for symmetric transformed Lyapunov residuals, the min-eigen xi-squared
    estimate has the sharp constant obtained from the paired summation. -/
theorem lyapunovXiSq_symmetric_le_min_eigen_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hR : IsSymmetricFiniteMatrix R_tilde)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤
      frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hdenom_le : ∀ i j : Fin n,
      4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≤
        2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    nlinarith [sq_nonneg α, hLam i, hLam j]
  have hden : ∀ i j : Fin n,
      2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 ≠ 0 := by
    intro i j
    exact ne_of_gt (lt_of_lt_of_le hDenom (hdenom_le i j))
  have htwo :=
    two_mul_lyapunovXiSq_eq_simple_bound_of_symmetric n R_tilde lam α γ hR hden
  have hbound :=
    lyapunovXiSqSimpleBound_le_min_eigen_bound n R_tilde lam α γ lamStar
      hLam hDenom
  let B : ℝ := frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)
  have hbound' :
      lyapunovXiSqSimpleBound n R_tilde lam α γ ≤ 2 * B := by
    dsimp [B]
    simpa [mul_div_assoc] using hbound
  have htwobound : 2 * lyapunovXiSq n R_tilde lam α γ ≤ 2 * B := by
    simpa [htwo] using hbound'
  nlinarith

/-- Lyapunov xi-squared residual bound after the orthogonal spectral transform
    `R_tilde = U^T R U`. -/
theorem lyapunovXiSq_spectral_le_min_eigen_bound (n : ℕ)
    (R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
      2 * frobNormSq R / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hle :=
    lyapunovXiSq_le_min_eigen_bound n (lyapunovSpectralTransform n U R) lam
      α γ lamStar hLam hDenom
  rw [lyapunovSpectralTransform_frobNormSq n U R hU] at hle
  exact hle

/-- Lyapunov xi-squared residual bound after an orthogonal spectral transform,
    sharpened for symmetric residuals. -/
theorem lyapunovXiSq_spectral_symmetric_le_min_eigen_bound (n : ℕ)
    (R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hR : IsSymmetricFiniteMatrix R)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
      frobNormSq R / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hle :=
    lyapunovXiSq_symmetric_le_min_eigen_bound n
      (lyapunovSpectralTransform n U R) lam α γ lamStar
      (lyapunovSpectralTransform_symmetric n U R hR) hLam hDenom
  rw [lyapunovSpectralTransform_frobNormSq n U R hU] at hle
  exact hle

/-- Higham, 2nd ed., Chapter 16.2.1, final display:
    the Lyapunov xi-squared residual bound written with the source amplification
    factor `mu`.  This is still an xi-level result; the eta optimizer bridge
    remains open. -/
theorem lyapunovXiSq_le_mu_relative_residual_sq (n : ℕ)
    (Y R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)
    (hScale : 0 < 2 * α * frobNorm Y + γ) :
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
      (lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
        (frobNorm R / (2 * α * frobNorm Y + γ))) ^ 2 := by
  have hle :=
    lyapunovXiSq_spectral_le_min_eigen_bound n R U lam α γ lamStar
      hU hLam hDenom
  have hScale_ne : 2 * α * frobNorm Y + γ ≠ 0 := ne_of_gt hScale
  have hSqrt_ne : Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hDenom)
  have hSqrt_sq :
      Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) ^ 2 =
        4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 :=
    Real.sq_sqrt (le_of_lt hDenom)
  have hsqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by linarith)
  calc
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
        2 * frobNormSq R / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := hle
    _ = (lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
        (frobNorm R / (2 * α * frobNorm Y + γ))) ^ 2 := by
        unfold lyapunovAmplificationMu
        have hmul :
            (Real.sqrt 2 * (2 * α * frobNorm Y + γ) /
                Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) *
              (frobNorm R / (2 * α * frobNorm Y + γ)) =
                Real.sqrt 2 * frobNorm R /
                  Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
          field_simp [hScale_ne, hSqrt_ne]
        rw [hmul, div_pow, mul_pow, hsqrt_two_sq, hSqrt_sq, frobNorm_sq]

/-- Higham, 2nd ed., Chapter 16.2.1, final Lyapunov display:
    square-root form of the Lyapunov xi residual amplification bound. -/
theorem sqrt_lyapunovXiSq_le_mu_relative_residual (n : ℕ)
    (Y R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)
    (hScale : 0 < 2 * α * frobNorm Y + γ) :
    Real.sqrt (lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ) ≤
      lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
        (frobNorm R / (2 * α * frobNorm Y + γ)) := by
  let kappa :=
    lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
      (frobNorm R / (2 * α * frobNorm Y + γ))
  have hxi :
      lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
        kappa ^ 2 := by
    simpa [kappa] using
      lyapunovXiSq_le_mu_relative_residual_sq n Y R U lam α γ lamStar
        hU hLam hDenom hScale
  have hmu_nonneg :
      0 ≤ lyapunovAmplificationMu α γ (frobNorm Y) lamStar := by
    unfold lyapunovAmplificationMu
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hScale))
      (Real.sqrt_nonneg _)
  have hrel_nonneg :
      0 ≤ frobNorm R / (2 * α * frobNorm Y + γ) :=
    div_nonneg (frobNorm_nonneg R) (le_of_lt hScale)
  have hkappa_nonneg : 0 ≤ kappa := by
    dsimp [kappa]
    exact mul_nonneg hmu_nonneg hrel_nonneg
  have hsqrt := Real.sqrt_le_sqrt hxi
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hkappa_nonneg] at hsqrt
  simpa [kappa] using hsqrt










































































































end NumStability
