import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Normwise

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Higham, 2nd ed., Chapter 20, equation (20.20): the weighted perturbation
    block `[DeltaA, theta Delta b]` used in the Frobenius normwise
    least-squares backward error. -/
noncomputable def lsNormwiseBackwardErrorWeightedMatrix {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    Fin m → Fin (n + 1) → ℝ :=
  fun i => Fin.append (DeltaA i) (fun _ : Fin 1 => theta * Deltab i)
/-- Cost term `||[DeltaA, theta Delta b]||_F` from Higham's definition
    (20.20) of the normwise least-squares backward error. -/
noncomputable def lsNormwiseBackwardErrorCostF {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : ℝ :=
  frobNormRect (lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab)
/-- Feasibility predicate for Higham's normwise least-squares backward error
    (20.20): `y` is an exact least-squares minimizer for the perturbed data
    `(A + DeltaA, b + Deltab)`. -/
def LSNormwiseBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  IsLeastSquaresMinimizer
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y
/-- Feasible-graph closedness for the (20.20) perturbation predicate: for
    fixed source data and candidate `y`, the perturbation pairs for which `y`
    is an exact least-squares minimizer form a closed set.  This is the
    finite-dimensional closed-graph ingredient for the later compactness proof;
    it does not prove the attainable-cost value set is closed or that the
    infimum is attained. -/
theorem LSNormwiseBackwardErrorFeasible.isClosed_set {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    IsClosed {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
      LSNormwiseBackwardErrorFeasible A b y p.1 p.2} := by
  rw [show {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
      LSNormwiseBackwardErrorFeasible A b y p.1 p.2} =
        ⋂ z : Fin n → ℝ,
          {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
            lsObjective (fun i j => A i j + p.1 i j)
                (fun i => b i + p.2 i) y ≤
              lsObjective (fun i j => A i j + p.1 i j)
                (fun i => b i + p.2 i) z} by
    ext p
    simp [LSNormwiseBackwardErrorFeasible, IsLeastSquaresMinimizer]]
  exact isClosed_iInter fun z =>
    isClosed_le (by
      unfold lsObjective lsResidual vecNorm2Sq rectMatMulVec
      fun_prop)
      (by
        unfold lsObjective lsResidual vecNorm2Sq rectMatMulVec
        fun_prop)
/-- Limit-closed form of `LSNormwiseBackwardErrorFeasible.isClosed_set`: a
    convergent net of feasible perturbation pairs has a feasible perturbation
    pair as its limit.  This is intended for the later compactness/subsequence
    route toward minimum-attainment in (20.20). -/
theorem LSNormwiseBackwardErrorFeasible.of_tendsto_pair
    {ι : Type*} {l : Filter ι} [l.NeBot] {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (pseq : ι → (Fin m → Fin n → ℝ) × (Fin m → ℝ))
    (p : (Fin m → Fin n → ℝ) × (Fin m → ℝ))
    (hfeas : Filter.Eventually
      (fun k => LSNormwiseBackwardErrorFeasible A b y (pseq k).1 (pseq k).2) l)
    (hp : Filter.Tendsto pseq l (nhds p)) :
    LSNormwiseBackwardErrorFeasible A b y p.1 p.2 := by
  exact (LSNormwiseBackwardErrorFeasible.isClosed_set A b y).mem_of_tendsto
    hp hfeas
/-- The set of attainable costs in Higham's normwise backward error
    definition (20.20).  The source writes a minimum; this exact model records
    the corresponding set, leaving minimum-attainment and the SVD formula
    (20.21) as separate spectral work. -/
noncomputable def lsNormwiseBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}
/-- Infimum model of Higham's normwise least-squares backward error `eta_F(y)`
    from (20.20).  Proving the source minimum formula and the alternative SVD
    expression (20.21) is left to the spectral backward-error row. -/
noncomputable def lsNormwiseBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (lsNormwiseBackwardErrorValuesF theta A b y)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5: the scalar
    `mu = theta^2 ||y||_2^2 / (1 + theta^2 ||y||_2^2)` used in the
    Walden--Karlson--Sun formula and its alternative form (20.21). -/
noncomputable def lsNormwiseBackwardErrorMu {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y)
/-- The denominator in the source scalar `mu` from Theorem 20.5 is positive. -/
theorem lsNormwiseBackwardErrorMu_den_pos {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    0 < 1 + theta ^ 2 * vecNorm2Sq y := by
  have hterm : 0 ≤ theta ^ 2 * vecNorm2Sq y :=
    mul_nonneg (sq_nonneg theta) (vecNorm2Sq_nonneg y)
  linarith
/-- The scalar `mu` in Theorem 20.5 is nonnegative. -/
theorem lsNormwiseBackwardErrorMu_nonneg {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    0 ≤ lsNormwiseBackwardErrorMu theta y := by
  unfold lsNormwiseBackwardErrorMu
  exact div_nonneg
    (mul_nonneg (sq_nonneg theta) (vecNorm2Sq_nonneg y))
    (le_of_lt (lsNormwiseBackwardErrorMu_den_pos theta y))
/-- The scalar `mu` in Theorem 20.5 is strictly below one. -/
theorem lsNormwiseBackwardErrorMu_lt_one {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorMu theta y < 1 := by
  unfold lsNormwiseBackwardErrorMu
  have hden : 0 < 1 + theta ^ 2 * vecNorm2Sq y :=
    lsNormwiseBackwardErrorMu_den_pos theta y
  rw [div_lt_iff₀ hden]
  nlinarith
/-- The scalar `mu` in Theorem 20.5 lies in `[0,1]`. -/
theorem lsNormwiseBackwardErrorMu_le_one {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorMu theta y ≤ 1 :=
  le_of_lt (lsNormwiseBackwardErrorMu_lt_one theta y)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5 limiting discussion:
    the source scalar `mu` is `1 - 1/(1 + theta^2 ||y||_2^2)`, making the
    `theta -> infinity` limit algebraically explicit. -/
theorem lsNormwiseBackwardErrorMu_eq_one_sub_inv_den {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorMu theta y =
      1 - 1 / (1 + theta ^ 2 * vecNorm2Sq y) := by
  unfold lsNormwiseBackwardErrorMu
  have hden : (1 + theta ^ 2 * vecNorm2Sq y) ≠ 0 :=
    ne_of_gt (lsNormwiseBackwardErrorMu_den_pos theta y)
  field_simp [hden]
  ring
/-- Equivalent residual form of the `mu` limiting identity:
    `1 - mu = 1/(1 + theta^2 ||y||_2^2)`. -/
theorem one_sub_lsNormwiseBackwardErrorMu_eq_inv_den {n : ℕ} (theta : ℝ)
    (y : Fin n → ℝ) :
    1 - lsNormwiseBackwardErrorMu theta y =
      1 / (1 + theta ^ 2 * vecNorm2Sq y) := by
  rw [lsNormwiseBackwardErrorMu_eq_one_sub_inv_den theta y]
  ring
/-- Higham, 2nd ed., Chapter 20, equation (20.21): the source scalar
    `phi = sqrt(mu) ||r||_2 / ||y||_2` used in the alternative normwise
    backward-error formula.  This definition only records the scalar appearing
    in the source formula; the singular-value minimization theorem remains a
    separate open spectral row. -/
noncomputable def lsNormwiseBackwardErrorPhi {m n : ℕ} (theta : ℝ)
    (r : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt (lsNormwiseBackwardErrorMu theta y) * vecNorm2 r / vecNorm2 y
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5: Hermitian matrix in the
    alternative eigenvalue expression for the Walden--Karlson--Sun normwise
    backward error,
    `A A^T - mu * r r^T / ||y||_2^2`. -/
noncomputable def lsNormwiseBackwardErrorEigenMatrix {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i k =>
    (∑ j : Fin n, A i j * A k j) -
      lsNormwiseBackwardErrorMu theta y * ((r i * r k) / vecNorm2Sq y)
/-- The source matrix `A A^T - mu * r r^T / ||y||_2^2` is symmetric. -/
theorem lsNormwiseBackwardErrorEigenMatrix_apply_comm {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ)
    (i k : Fin m) :
    lsNormwiseBackwardErrorEigenMatrix theta A r y i k =
      lsNormwiseBackwardErrorEigenMatrix theta A r y k i := by
  have hgram :
      (∑ j : Fin n, A i j * A k j) =
        ∑ j : Fin n, A k j * A i j := by
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have houter : r i * r k / vecNorm2Sq y = r k * r i / vecNorm2Sq y := by
    ring
  simp [lsNormwiseBackwardErrorEigenMatrix, hgram, houter]
/-- The eigenvalue-branch source matrix in Higham's Theorem 20.5 is Hermitian,
    so Mathlib's Hermitian eigenvalue API applies. -/
theorem lsNormwiseBackwardErrorEigenMatrix_isHermitian {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    (lsNormwiseBackwardErrorEigenMatrix theta A r y).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i k
  simp [lsNormwiseBackwardErrorEigenMatrix_apply_comm theta A r y k i]
/-- Ordered Hermitian eigenvalue index corresponding to the last row index of
    an `(m+1) x (m+1)` source matrix. -/
def lsNormwiseBackwardErrorLambdaStarIndex (m : ℕ) :
    Fin (Fintype.card (Fin (m + 1))) :=
  ⟨m, by simp⟩
/-- Every ordered Hermitian eigenvalue index precedes the source last index. -/
theorem le_lsNormwiseBackwardErrorLambdaStarIndex (m : ℕ)
    (i : Fin (Fintype.card (Fin (m + 1)))) :
    i ≤ lsNormwiseBackwardErrorLambdaStarIndex m := by
  rw [Fin.le_iff_val_le_val]
  change (i : ℕ) ≤ m
  exact Nat.lt_succ_iff.mp (by simpa using i.isLt)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5: `lambda_*`, the smallest
    Hermitian eigenvalue of `A A^T - mu * r r^T / ||y||_2^2`.  Mathlib orders
    Hermitian eigenvalues antitonically, so the source last index is the
    `lambda_min` index. -/
noncomputable def lsNormwiseBackwardErrorLambdaStar {m n : ℕ} (theta : ℝ)
    (A : Fin (m + 1) → Fin n → ℝ) (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ) :
    ℝ :=
  (lsNormwiseBackwardErrorEigenMatrix_isHermitian theta A r y).eigenvalues₀
    (lsNormwiseBackwardErrorLambdaStarIndex m)
/-- The `lambda_*` index is the least member of Mathlib's antitone Hermitian
    eigenvalue list. -/
theorem lsNormwiseBackwardErrorLambdaStar_le_eigenvalues₀ {m n : ℕ}
    (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (i : Fin (Fintype.card (Fin (m + 1)))) :
    lsNormwiseBackwardErrorLambdaStar theta A r y ≤
      (lsNormwiseBackwardErrorEigenMatrix_isHermitian theta A r y).eigenvalues₀ i := by
  unfold lsNormwiseBackwardErrorLambdaStar
  exact (Matrix.IsHermitian.eigenvalues₀_antitone
      (lsNormwiseBackwardErrorEigenMatrix_isHermitian theta A r y))
    (le_lsNormwiseBackwardErrorLambdaStarIndex m i)
/-- Source-facing least-eigenvalue statement for Higham's `lambda_*`: among
    the Hermitian eigenvalues of `A A^T - mu * r r^T / ||y||_2^2`, `lambda_*`
    is least. -/
theorem lsNormwiseBackwardErrorLambdaStar_isLeast_eigenvalues₀_range {m n : ℕ}
    (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ) :
    IsLeast
      (Set.range fun i : Fin (Fintype.card (Fin (m + 1))) =>
        (lsNormwiseBackwardErrorEigenMatrix_isHermitian theta A r y).eigenvalues₀ i)
      (lsNormwiseBackwardErrorLambdaStar theta A r y) := by
  refine ⟨?_, ?_⟩
  · exact ⟨lsNormwiseBackwardErrorLambdaStarIndex m, by
      simp [lsNormwiseBackwardErrorLambdaStar]⟩
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact lsNormwiseBackwardErrorLambdaStar_le_eigenvalues₀ theta A r y i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5: the nonnegative-`lambda_*`
    branch `||r||_2 / ||y||_2 * sqrt(mu)`. -/
noncomputable def lsNormwiseBackwardErrorEigenvalueNonnegativeBranch {m n : ℕ}
    (theta : ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  vecNorm2 r / vecNorm2 y * Real.sqrt (lsNormwiseBackwardErrorMu theta y)
/-- The printed nonnegative eigenvalue branch is the same scalar as the
    `phi` term used in equation (20.21). -/
theorem lsNormwiseBackwardErrorEigenvalueNonnegativeBranch_eq_phi {m n : ℕ}
    (theta : ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEigenvalueNonnegativeBranch theta r y =
      lsNormwiseBackwardErrorPhi theta r y := by
  unfold lsNormwiseBackwardErrorEigenvalueNonnegativeBranch
    lsNormwiseBackwardErrorPhi
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5: the displayed eigenvalue
    formula for the finite-`theta` WKS normwise backward-error value, recorded
    for a supplied residual vector `r`.  The equality with `eta_F(y)` remains
    a separate theorem row. -/
noncomputable def lsNormwiseBackwardErrorEigenvalueFormulaValue {m n : ℕ}
    (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ) : ℝ :=
  let lambdaStar := lsNormwiseBackwardErrorLambdaStar theta A r y
  if 0 ≤ lambdaStar then
    lsNormwiseBackwardErrorEigenvalueNonnegativeBranch theta r y
  else
    Real.sqrt
      ((vecNorm2Sq r / vecNorm2Sq y) * lsNormwiseBackwardErrorMu theta y +
        lambdaStar)
/-- Source-data form of Higham's Theorem 20.5 eigenvalue expression, using
    the residual convention `r = b - A*y`. -/
noncomputable def lsNormwiseBackwardErrorEigenvalueFormulaRHS {m n : ℕ}
    (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (b : Fin (m + 1) → ℝ) (y : Fin n → ℝ) : ℝ :=
  lsNormwiseBackwardErrorEigenvalueFormulaValue theta A (lsResidualHigham A b y) y
/-- When `lambda_* >= 0`, the eigenvalue formula reduces to the source scalar
    `phi`. -/
theorem lsNormwiseBackwardErrorEigenvalueFormulaValue_eq_phi_of_lambdaStar_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (hlambda : 0 ≤ lsNormwiseBackwardErrorLambdaStar theta A r y) :
    lsNormwiseBackwardErrorEigenvalueFormulaValue theta A r y =
      lsNormwiseBackwardErrorPhi theta r y := by
  simp [lsNormwiseBackwardErrorEigenvalueFormulaValue, hlambda,
    lsNormwiseBackwardErrorEigenvalueNonnegativeBranch_eq_phi]
/-- When `lambda_* < 0`, the eigenvalue formula selects the printed square-root
    branch from Theorem 20.5. -/
theorem lsNormwiseBackwardErrorEigenvalueFormulaValue_eq_sqrt_of_lambdaStar_neg
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (hlambda : lsNormwiseBackwardErrorLambdaStar theta A r y < 0) :
    lsNormwiseBackwardErrorEigenvalueFormulaValue theta A r y =
      Real.sqrt
        ((vecNorm2Sq r / vecNorm2Sq y) * lsNormwiseBackwardErrorMu theta y +
          lsNormwiseBackwardErrorLambdaStar theta A r y) := by
  have hnot : ¬ 0 ≤ lsNormwiseBackwardErrorLambdaStar theta A r y :=
    not_le_of_gt hlambda
  simp [lsNormwiseBackwardErrorEigenvalueFormulaValue, hnot]
/-- Source-data nonnegative-`lambda_*` branch of the eigenvalue expression:
    with `r = b - A*y`, the Theorem 20.5 eigenvalue RHS is the scalar `phi`
    branch. -/
theorem lsNormwiseBackwardErrorEigenvalueFormulaRHS_eq_phi_of_lambdaStar_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (b : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (hlambda :
      0 ≤ lsNormwiseBackwardErrorLambdaStar theta A (lsResidualHigham A b y) y) :
    lsNormwiseBackwardErrorEigenvalueFormulaRHS theta A b y =
      lsNormwiseBackwardErrorPhi theta (lsResidualHigham A b y) y := by
  simpa [lsNormwiseBackwardErrorEigenvalueFormulaRHS] using
    lsNormwiseBackwardErrorEigenvalueFormulaValue_eq_phi_of_lambdaStar_nonneg
      theta A (lsResidualHigham A b y) y hlambda
/-- Source-data negative-`lambda_*` branch of the eigenvalue expression from
    Theorem 20.5. -/
theorem lsNormwiseBackwardErrorEigenvalueFormulaRHS_eq_sqrt_of_lambdaStar_neg
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (b : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (hlambda :
      lsNormwiseBackwardErrorLambdaStar theta A (lsResidualHigham A b y) y < 0) :
    lsNormwiseBackwardErrorEigenvalueFormulaRHS theta A b y =
      Real.sqrt
        ((vecNorm2Sq (lsResidualHigham A b y) / vecNorm2Sq y) *
            lsNormwiseBackwardErrorMu theta y +
          lsNormwiseBackwardErrorLambdaStar theta A (lsResidualHigham A b y) y) := by
  simpa [lsNormwiseBackwardErrorEigenvalueFormulaRHS] using
    lsNormwiseBackwardErrorEigenvalueFormulaValue_eq_sqrt_of_lambdaStar_neg
      theta A (lsResidualHigham A b y) y hlambda
/-- The source scalar `phi` from (20.21) is nonnegative. -/
theorem lsNormwiseBackwardErrorPhi_nonneg {m n : ℕ} (theta : ℝ)
    (r : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ lsNormwiseBackwardErrorPhi theta r y := by
  unfold lsNormwiseBackwardErrorPhi
  exact div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (vecNorm2_nonneg r))
    (vecNorm2_nonneg y)
/-- If the residual vector in the displayed right-hand side of (20.21) is zero,
    then the scalar branch `phi` is zero. -/
theorem lsNormwiseBackwardErrorPhi_eq_zero_of_residual_eq_zero {m n : ℕ}
    (theta : ℝ) {r : Fin m → ℝ} (y : Fin n → ℝ) (hr : r = 0) :
    lsNormwiseBackwardErrorPhi theta r y = 0 := by
  subst r
  unfold lsNormwiseBackwardErrorPhi
  have hzero : vecNorm2 (0 : Fin m → ℝ) = 0 := by
    simpa using (vecNorm2_zero (n := m))
  rw [hzero]
  ring
/-- The Frobenius cost in (20.20) is nonnegative. -/
theorem lsNormwiseBackwardErrorCostF_nonneg {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    0 ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
  frobNormRect_nonneg _
/-- Squared Frobenius norm of the weighted perturbation block
    `[DeltaA, theta Delta b]` in Higham's definition (20.20). -/
theorem lsNormwiseBackwardErrorWeightedMatrix_frobNormSqRect {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    frobNormSqRect (lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab) =
      frobNormSqRect DeltaA + theta ^ 2 * vecNorm2Sq Deltab := by
  have hrow : ∀ i : Fin m,
      (∑ j : Fin (n + 1),
          lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab i j ^ 2) =
        (∑ j : Fin n, DeltaA i j ^ 2) + (theta * Deltab i) ^ 2 := by
    intro i
    rw [Fin.sum_univ_add]
    simp [lsNormwiseBackwardErrorWeightedMatrix, Fin.append_left, Fin.append_right]
  unfold frobNormSqRect vecNorm2Sq
  calc
    ∑ i : Fin m,
        ∑ j : Fin (n + 1),
          lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab i j ^ 2 =
        ∑ i : Fin m, ((∑ j : Fin n, DeltaA i j ^ 2) + (theta * Deltab i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hrow i
    _ = (∑ i : Fin m, ∑ j : Fin n, DeltaA i j ^ 2) +
          ∑ i : Fin m, (theta * Deltab i) ^ 2 := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, ∑ j : Fin n, DeltaA i j ^ 2) +
          theta ^ 2 * ∑ i : Fin m, Deltab i ^ 2 := by
          congr 1
          calc
            ∑ i : Fin m, (theta * Deltab i) ^ 2 =
                ∑ i : Fin m, theta ^ 2 * Deltab i ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = theta ^ 2 * ∑ i : Fin m, Deltab i ^ 2 := by
              rw [Finset.mul_sum]
/-- Squared cost form of Higham's weighted Frobenius perturbation norm in
    (20.20). -/
theorem lsNormwiseBackwardErrorCostF_sq {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab ^ 2 =
      frobNormSqRect DeltaA + theta ^ 2 * vecNorm2Sq Deltab := by
  rw [lsNormwiseBackwardErrorCostF, frobNormRect_sq,
    lsNormwiseBackwardErrorWeightedMatrix_frobNormSqRect]
/-- Monotonicity of the weighted Frobenius perturbation cost in (20.20):
    increasing a nonnegative source weight `theta` cannot decrease
    `||[DeltaA, theta Delta b]||_F`. -/
theorem lsNormwiseBackwardErrorCostF_mono_theta_nonneg {m n : ℕ}
    {theta1 theta2 : ℝ} (htheta1 : 0 ≤ theta1) (htheta12 : theta1 ≤ theta2)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF theta1 DeltaA Deltab ≤
      lsNormwiseBackwardErrorCostF theta2 DeltaA Deltab := by
  have htheta2 : 0 ≤ theta2 := le_trans htheta1 htheta12
  have hsqs : theta1 ^ 2 ≤ theta2 ^ 2 := by
    exact (sq_le_sq).mpr (by
      simpa [abs_of_nonneg htheta1, abs_of_nonneg htheta2] using htheta12)
  have hsq :
      lsNormwiseBackwardErrorCostF theta1 DeltaA Deltab ^ 2 ≤
        lsNormwiseBackwardErrorCostF theta2 DeltaA Deltab ^ 2 := by
    rw [lsNormwiseBackwardErrorCostF_sq, lsNormwiseBackwardErrorCostF_sq]
    have hmul :=
      mul_le_mul_of_nonneg_right hsqs (vecNorm2Sq_nonneg Deltab)
    nlinarith [hmul]
  have hleft : 0 ≤ lsNormwiseBackwardErrorCostF theta1 DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_nonneg theta1 DeltaA Deltab
  have hright : 0 ≤ lsNormwiseBackwardErrorCostF theta2 DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_nonneg theta2 DeltaA Deltab
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5 discussion after (20.20):
    the weighted Frobenius cost controls the weighted right-hand-side
    perturbation.  This is the finite-`theta` inequality behind the source
    comment that taking `theta → ∞` forces `Delta b = 0`. -/
theorem lsNormwiseBackwardErrorCostF_weighted_deltab_le {m n : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    theta * vecNorm2 Deltab ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  have hsq :
      (theta * vecNorm2 Deltab) ^ 2 ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab ^ 2 := by
    rw [lsNormwiseBackwardErrorCostF_sq, ← vecNorm2_sq Deltab]
    nlinarith [frobNormSqRect_nonneg DeltaA]
  have hleft : 0 ≤ theta * vecNorm2 Deltab :=
    mul_nonneg htheta (vecNorm2_nonneg Deltab)
  have hright : 0 ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs
/-- The weighted Frobenius perturbation cost in (20.20) also controls the
    matrix perturbation block `DeltaA`. -/
theorem lsNormwiseBackwardErrorCostF_deltaA_le {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    frobNormRect DeltaA ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  have hsq :
      frobNormRect DeltaA ^ 2 ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab ^ 2 := by
    rw [frobNormRect_sq, lsNormwiseBackwardErrorCostF_sq]
    have hterm : 0 ≤ theta ^ 2 * vecNorm2Sq Deltab :=
      mul_nonneg (sq_nonneg theta) (vecNorm2Sq_nonneg Deltab)
    nlinarith
  have hleft : 0 ≤ frobNormRect DeltaA := frobNormRect_nonneg DeltaA
  have hright : 0 ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs
/-- Positive-`theta` divided form of
    `lsNormwiseBackwardErrorCostF_weighted_deltab_le`: any bounded weighted
    perturbation cost bounds `||Delta b||₂` by `cost / theta`. -/
theorem lsNormwiseBackwardErrorDeltab_norm_le_cost_div_theta {m n : ℕ}
    {theta : ℝ} (htheta : 0 < theta)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    vecNorm2 Deltab ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab / theta := by
  rw [le_div_iff₀ htheta]
  simpa [mul_comm] using
    lsNormwiseBackwardErrorCostF_weighted_deltab_le
      (le_of_lt htheta) DeltaA Deltab
/-- Coercivity component for (20.20): the weighted Frobenius perturbation cost
    controls every entry of the matrix perturbation. -/
theorem lsNormwiseBackwardErrorCostF_deltaA_entry_abs_le {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (i : Fin m) (j : Fin n) :
    |DeltaA i j| ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
  (abs_entry_le_frobNormRect DeltaA i j).trans
    (lsNormwiseBackwardErrorCostF_deltaA_le theta DeltaA Deltab)
/-- Coercivity component for (20.20): for nonnegative `theta`, the weighted
    Frobenius perturbation cost controls each weighted right-hand-side entry. -/
theorem lsNormwiseBackwardErrorCostF_weighted_deltab_entry_abs_le
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) (i : Fin m) :
    theta * |Deltab i| ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  exact
    (mul_le_mul_of_nonneg_left (abs_coord_le_vecNorm2 Deltab i) htheta).trans
      (lsNormwiseBackwardErrorCostF_weighted_deltab_le htheta DeltaA Deltab)
/-- Positive-`theta` pointwise form of the right-hand-side coercivity bound:
    each `Delta b` entry is controlled by the weighted Frobenius cost divided
    by `theta`. -/
theorem lsNormwiseBackwardErrorCostF_deltab_entry_abs_le_cost_div_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) (i : Fin m) :
    |Deltab i| ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab / theta := by
  rw [le_div_iff₀ htheta]
  simpa [mul_comm] using
    lsNormwiseBackwardErrorCostF_weighted_deltab_entry_abs_le
      (le_of_lt htheta) DeltaA Deltab i
/-- Expanded square-root form of the Frobenius cost
    `||[DeltaA, theta Delta b]||_F` in (20.20). -/
theorem lsNormwiseBackwardErrorCostF_eq_sqrt_sq_sum {m n : ℕ} (theta : ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
      Real.sqrt (frobNormSqRect DeltaA + theta ^ 2 * vecNorm2Sq Deltab) := by
  rw [lsNormwiseBackwardErrorCostF, frobNormRect,
    lsNormwiseBackwardErrorWeightedMatrix_frobNormSqRect]
/-- Matrix-only specialization of the weighted cost in (20.20): when
    `Delta b = 0`, the finite-`theta` cost is exactly `||DeltaA||_F`.  This is
    the finite-cost algebra behind the source convention that the
    `theta = infinity` case forbids right-hand-side perturbations. -/
theorem lsNormwiseBackwardErrorCostF_eq_frobNormRect_of_deltab_zero
    {m n : ℕ} (theta : ℝ) (DeltaA : Fin m → Fin n → ℝ) :
    lsNormwiseBackwardErrorCostF theta DeltaA (0 : Fin m → ℝ) =
      frobNormRect DeltaA := by
  rw [lsNormwiseBackwardErrorCostF_eq_sqrt_sq_sum]
  simp [vecNorm2Sq, frobNormRect]
/-- The weighted perturbation block in (20.20) applied to the vector
    `[theta y; -1]` produces `theta * (DeltaA y - Delta b)`.  This is the
    Cauchy--Schwarz witness behind the exact-residual branch of the WKS
    lower-bound proof. -/
theorem lsNormwiseBackwardErrorWeightedMatrix_mulVec_phi_witness {m n : ℕ}
    (theta : ℝ) (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (y : Fin n → ℝ) :
    rectMatMulVec (lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab)
        (Fin.append (fun j : Fin n => theta * y j) (fun _ : Fin 1 => -1)) =
      fun i : Fin m => theta * (rectMatMulVec DeltaA y i - Deltab i) := by
  ext i
  unfold rectMatMulVec
  rw [Fin.sum_univ_add]
  simp [lsNormwiseBackwardErrorWeightedMatrix, Fin.append_left,
    Fin.append_right]
  change
    (∑ x : Fin n, DeltaA i x * (theta * y x)) + -(theta * Deltab i) =
      theta * ((∑ j : Fin n, DeltaA i j * y j) - Deltab i)
  calc
    (∑ x : Fin n, DeltaA i x * (theta * y x)) + -(theta * Deltab i)
        = theta * (∑ x : Fin n, DeltaA i x * y x) - theta * Deltab i := by
          congr 1
          calc
            ∑ x : Fin n, DeltaA i x * (theta * y x) =
                ∑ x : Fin n, theta * (DeltaA i x * y x) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
            _ = theta * (∑ x : Fin n, DeltaA i x * y x) := by
                  rw [Finset.mul_sum]
    _ = theta * ((∑ j : Fin n, DeltaA i j * y j) - Deltab i) := by
          ring
/-- Euclidean norm of the WKS exact-residual witness vector `[theta y; -1]`. -/
theorem lsNormwiseBackwardErrorWeightedWitness_vecNorm2 {n : ℕ}
    (theta : ℝ) (y : Fin n → ℝ) :
    vecNorm2
        (Fin.append (fun j : Fin n => theta * y j) (fun _ : Fin 1 => -1)) =
      Real.sqrt (1 + theta ^ 2 * vecNorm2Sq y) := by
  unfold vecNorm2 vecNorm2Sq
  congr 1
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
  rw [Finset.mul_sum]
  ring_nf
/-- Rank-one perturbation used in the constructive WKS upper-bound route.  For
    nonzero `p`, its transpose action on `p` realizes `-u`. -/
noncomputable def lsNormwiseBackwardErrorRankOneDeltaA {m n : ℕ}
    (p : Fin m → ℝ) (u : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => -((1 / vecNorm2Sq p) * p i * u j)
/-- The rank-one WKS perturbation realizes the prescribed left source-block
    action on a nonzero expanded residual. -/
theorem lsNormwiseBackwardErrorRankOneDeltaA_transpose_mul
    {m n : ℕ} {p : Fin m → ℝ} {u : Fin n → ℝ}
    (hp : vecNorm2Sq p ≠ 0) :
    (fun j : Fin n =>
      ∑ i : Fin m, lsNormwiseBackwardErrorRankOneDeltaA p u i j * p i) =
      fun j => -u j := by
  ext j
  have hinv : (1 / vecNorm2Sq p) * vecNorm2Sq p = 1 := by
    field_simp [hp]
  calc
    ∑ i : Fin m, lsNormwiseBackwardErrorRankOneDeltaA p u i j * p i
        = ∑ i : Fin m, (-(1 / vecNorm2Sq p) * u j) * p i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            simp [lsNormwiseBackwardErrorRankOneDeltaA]
            ring
    _ = (-(1 / vecNorm2Sq p) * u j) * ∑ i : Fin m, p i ^ 2 := by
            rw [Finset.mul_sum]
    _ = -u j := by
            change (-(1 / vecNorm2Sq p) * u j) * vecNorm2Sq p = -u j
            calc
              (-(1 / vecNorm2Sq p) * u j) * vecNorm2Sq p
                  = -u j * ((1 / vecNorm2Sq p) * vecNorm2Sq p) := by ring
              _ = -u j := by
                    rw [hinv]
                    ring
/-- Matrix-vector action of the rank-one WKS perturbation.  This exposes the
    `DeltaA * y` term in the constructive upper-bound witness cost. -/
theorem lsNormwiseBackwardErrorRankOneDeltaA_mulVec
    {m n : ℕ} (p : Fin m → ℝ) (u y : Fin n → ℝ) :
    rectMatMulVec (lsNormwiseBackwardErrorRankOneDeltaA p u) y =
      fun i : Fin m =>
        -((1 / vecNorm2Sq p) * p i * (∑ j : Fin n, u j * y j)) := by
  ext i
  unfold rectMatMulVec lsNormwiseBackwardErrorRankOneDeltaA
  calc
    ∑ j : Fin n, -((1 / vecNorm2Sq p) * p i * u j) * y j
        = ∑ j : Fin n, (-((1 / vecNorm2Sq p) * p i)) * (u j * y j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (-((1 / vecNorm2Sq p) * p i)) * ∑ j : Fin n, u j * y j := by
            rw [Finset.mul_sum]
    _ = -((1 / vecNorm2Sq p) * p i * (∑ j : Fin n, u j * y j)) := by
            ring
/-- Continuity of the weighted Frobenius perturbation cost from (20.20) as a
    function of the perturbation pair.  Together with feasible-graph closedness
    and the entrywise bounded-sublevel lemmas, this is a local ingredient for
    the later finite-dimensional compactness/minimum-attainment argument. -/
theorem lsNormwiseBackwardErrorCostF_continuous_pair {m n : ℕ} (theta : ℝ) :
    Continuous fun p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) =>
      lsNormwiseBackwardErrorCostF theta p.1 p.2 := by
  have hcont : Continuous fun p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) =>
      Real.sqrt (frobNormSqRect p.1 + theta ^ 2 * vecNorm2Sq p.2) := by
    apply Real.continuous_sqrt.comp
    unfold frobNormSqRect vecNorm2Sq
    fun_prop
  simpa [lsNormwiseBackwardErrorCostF_eq_sqrt_sq_sum] using hcont
/-- Compactness of a bounded feasible perturbation-pair sublevel for the
    normwise backward-error model (20.20), for positive finite `theta`.  This
    combines feasible-graph closedness, cost continuity, and the entrywise
    Frobenius coercivity bounds; it is still only a compactness ingredient, not
    the source minimum-attainment theorem or formula (20.21). -/
theorem LSNormwiseBackwardErrorFeasible.cost_sublevel_isCompact
    {m n : ℕ} {theta R : ℝ} (htheta : 0 < theta) (hR : 0 ≤ R)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    IsCompact {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
      LSNormwiseBackwardErrorFeasible A b y p.1 p.2 ∧
        lsNormwiseBackwardErrorCostF theta p.1 p.2 ≤ R} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hfeas : IsClosed {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
        LSNormwiseBackwardErrorFeasible A b y p.1 p.2} :=
      LSNormwiseBackwardErrorFeasible.isClosed_set A b y
    have hcost : IsClosed {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) |
        lsNormwiseBackwardErrorCostF theta p.1 p.2 ≤ R} := by
      exact isClosed_le (lsNormwiseBackwardErrorCostF_continuous_pair theta)
        continuous_const
    simpa [Set.setOf_and] using hfeas.inter hcost
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨max R (R / theta), ?_⟩
    intro p hp
    rw [norm_prod_le_iff]
    constructor
    · have hA : ‖p.1‖ ≤ R := by
        rw [pi_norm_le_iff_of_nonneg hR]
        intro i
        rw [pi_norm_le_iff_of_nonneg hR]
        intro j
        simpa [Real.norm_eq_abs] using
          (lsNormwiseBackwardErrorCostF_deltaA_entry_abs_le
            theta p.1 p.2 i j).trans hp.2
      exact hA.trans (le_max_left R (R / theta))
    · have hdiv_nonneg : 0 ≤ R / theta := div_nonneg hR (le_of_lt htheta)
      have hb : ‖p.2‖ ≤ R / theta := by
        rw [pi_norm_le_iff_of_nonneg hdiv_nonneg]
        intro i
        have hentry :=
          lsNormwiseBackwardErrorCostF_deltab_entry_abs_le_cost_div_theta
            (m := m) (n := n) htheta p.1 p.2 i
        have hcost_div :
            lsNormwiseBackwardErrorCostF theta p.1 p.2 / theta ≤ R / theta := by
          exact div_le_div_of_nonneg_right hp.2 (le_of_lt htheta)
        simpa [Real.norm_eq_abs] using hentry.trans hcost_div
      exact hb.trans (le_max_right R (R / theta))
/-- Closedness of bounded attainable-cost sublevels for the normwise backward
    error value set (20.20), for positive finite `theta`.  This is the image of
    the compact feasible perturbation-pair sublevel under the continuous cost
    map.  It does not prove global value-set closedness, minimum-attainment, or
    the Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorValuesF.sublevel_isClosed
    {m n : ℕ} {theta R : ℝ} (htheta : 0 < theta) (hR : 0 ≤ R)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    IsClosed (lsNormwiseBackwardErrorValuesF theta A b y ∩ Set.Iic R) := by
  let cost : ((Fin m → Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun p => lsNormwiseBackwardErrorCostF theta p.1 p.2
  let feasibleSub : Set ((Fin m → Fin n → ℝ) × (Fin m → ℝ)) :=
    {p | LSNormwiseBackwardErrorFeasible A b y p.1 p.2 ∧ cost p ≤ R}
  have hcompact : IsCompact feasibleSub :=
    LSNormwiseBackwardErrorFeasible.cost_sublevel_isCompact
      (m := m) (n := n) htheta hR A b y
  have himage :
      cost '' feasibleSub =
        lsNormwiseBackwardErrorValuesF theta A b y ∩ Set.Iic R := by
    ext eta
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, p.2, hp.1, rfl⟩, hp.2⟩
    · rintro ⟨heta, heta_le⟩
      rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
      refine ⟨(DeltaA, Deltab), ?_, ?_⟩
      · exact ⟨hfeas, by simpa [cost, heta_eq] using heta_le⟩
      · simp [cost, heta_eq]
  have hcompact_image : IsCompact (cost '' feasibleSub) := by
    exact hcompact.image (by
      simpa [cost] using
        lsNormwiseBackwardErrorCostF_continuous_pair (m := m) (n := n) theta)
  rw [himage] at hcompact_image
  exact hcompact_image.isClosed
/-- Any feasible perturbation contributes its cost to the value set used in
    the `eta_F` model for (20.20). -/
theorem lsNormwiseBackwardErrorValuesF.mem_of_feasible {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∈
      lsNormwiseBackwardErrorValuesF theta A b y := by
  refine ⟨DeltaA, Deltab, hfeas, rfl⟩
/-- The zero perturbation has zero Frobenius cost in the (20.20) weighted
    block model. -/
theorem lsNormwiseBackwardErrorCostF_zero {m n : ℕ} (theta : ℝ) :
    lsNormwiseBackwardErrorCostF (m := m) (n := n) theta
      (0 : Fin m → Fin n → ℝ) (0 : Fin m → ℝ) = 0 := by
  simp [lsNormwiseBackwardErrorCostF, lsNormwiseBackwardErrorWeightedMatrix,
    frobNormRect, frobNormSqRect, Fin.sum_univ_add]
/-- In the weighted Frobenius perturbation block from (20.20), zero cost means
    that both perturbations vanish, provided the source weight `theta` is
    nonzero. -/
theorem lsNormwiseBackwardErrorCostF_eq_zero_iff {m n : ℕ} {theta : ℝ}
    (htheta : theta ≠ 0)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab = 0 ↔
      DeltaA = 0 ∧ Deltab = 0 := by
  constructor
  · intro hcost
    unfold lsNormwiseBackwardErrorCostF frobNormRect at hcost
    rw [Real.sqrt_eq_zero (frobNormSqRect_nonneg
      (lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab))] at hcost
    have hentries :=
      (frobNormSqRect_eq_zero_iff
        (lsNormwiseBackwardErrorWeightedMatrix theta DeltaA Deltab)).mp hcost
    constructor
    · ext i j
      have hleft := hentries i (Fin.castAdd 1 j)
      simpa [lsNormwiseBackwardErrorWeightedMatrix] using hleft
    · ext i
      have hright := hentries i (Fin.natAdd n (0 : Fin 1))
      have hmul : theta * Deltab i = 0 := by
        simpa [lsNormwiseBackwardErrorWeightedMatrix] using hright
      rcases mul_eq_zero.mp hmul with htheta_zero | hdeltab
      · exact False.elim (htheta htheta_zero)
      · exact hdeltab
  · intro hzero
    rcases hzero with ⟨hDeltaA, hDeltab⟩
    subst DeltaA
    subst Deltab
    exact lsNormwiseBackwardErrorCostF_zero theta
/-- The attainable-cost set in the (20.20) infimum model is nonempty.  One can
    annihilate the data with `DeltaA = -A` and `Deltab = -b`, making every `y`
    an exact least-squares minimizer for the perturbed problem. -/
theorem lsNormwiseBackwardErrorValuesF.nonempty {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    (lsNormwiseBackwardErrorValuesF theta A b y).Nonempty := by
  refine ⟨lsNormwiseBackwardErrorCostF theta (fun i j => -A i j) (fun i => -b i), ?_⟩
  apply lsNormwiseBackwardErrorValuesF.mem_of_feasible
  intro z
  simp [lsObjective, lsResidual, rectMatMulVec, vecNorm2Sq]
/-- The attainable-cost set in the (20.20) infimum model is bounded below by
    zero. -/
theorem lsNormwiseBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (lsNormwiseBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
/-- Every attainable cost in the (20.20) value set is nonnegative.  This
    localizes bounded value sublevels before the later compactness/closedness
    argument for minimum-attainment. -/
theorem lsNormwiseBackwardErrorValuesF.nonneg_of_mem {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorValuesF theta A b y) :
    0 ≤ eta := by
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
/-- A bounded attainable value for (20.20) lies in the compact interval shape
    `[0, R]`.  This is only a localization lemma for the future compactness
    proof; it does not prove the attainable-cost set is closed. -/
theorem lsNormwiseBackwardErrorValuesF.mem_Icc_of_mem_le {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta R : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorValuesF theta A b y)
    (heta_le : eta ≤ R) :
    eta ∈ Set.Icc 0 R :=
  ⟨lsNormwiseBackwardErrorValuesF.nonneg_of_mem theta A b y heta, heta_le⟩
/-- Bounded sublevels of the (20.20) attainable-cost set are contained in
    `[0, R]`.  This packages the order-theoretic part of the eventual
    finite-dimensional compactness argument. -/
theorem lsNormwiseBackwardErrorValuesF.sublevel_subset_Icc {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) (R : ℝ) :
    lsNormwiseBackwardErrorValuesF theta A b y ∩ Set.Iic R ⊆ Set.Icc 0 R := by
  intro eta heta
  exact lsNormwiseBackwardErrorValuesF.mem_Icc_of_mem_le theta A b y
    heta.1 heta.2
/-- The (20.20) infimum model `eta_F(y)` is nonnegative. -/
theorem lsNormwiseBackwardErrorEtaF_nonneg {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ lsNormwiseBackwardErrorEtaF theta A b y := by
  unfold lsNormwiseBackwardErrorEtaF
  apply Real.sInf_nonneg
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
/-- If `y` is already an exact minimizer for the original data, then zero is an
    attainable cost in the (20.20) value set. -/
theorem lsNormwiseBackwardErrorValuesF.zero_mem_of_isLeastSquaresMinimizer
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (hmin : IsLeastSquaresMinimizer A b y) :
    (0 : ℝ) ∈ lsNormwiseBackwardErrorValuesF theta A b y := by
  rw [← lsNormwiseBackwardErrorCostF_zero (m := m) (n := n) theta]
  apply lsNormwiseBackwardErrorValuesF.mem_of_feasible
  simpa [LSNormwiseBackwardErrorFeasible] using hmin
/-- For nonzero `theta`, zero is an attainable cost in the (20.20) value set
    exactly when `y` is already an exact least-squares minimizer for the
    original data. This is a minimum-attainment sanity check for the later
    Walden--Karlson--Sun formula, not that formula itself. -/
theorem lsNormwiseBackwardErrorValuesF.zero_mem_iff_isLeastSquaresMinimizer
    {m n : ℕ} {theta : ℝ} (htheta : theta ≠ 0)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    (0 : ℝ) ∈ lsNormwiseBackwardErrorValuesF theta A b y ↔
      IsLeastSquaresMinimizer A b y := by
  constructor
  · intro hzero
    rcases hzero with ⟨DeltaA, Deltab, hfeas, hcost⟩
    have hcost_zero :
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab = 0 := hcost.symm
    have hpert_zero :=
      (lsNormwiseBackwardErrorCostF_eq_zero_iff (m := m) (n := n)
        htheta DeltaA Deltab).mp hcost_zero
    rcases hpert_zero with ⟨hDeltaA, hDeltab⟩
    subst DeltaA
    subst Deltab
    simpa [LSNormwiseBackwardErrorFeasible] using hfeas
  · intro hmin
    exact lsNormwiseBackwardErrorValuesF.zero_mem_of_isLeastSquaresMinimizer
      theta A b y hmin
/-- If `y` is already an exact minimizer for the original data, then the
    (20.20) infimum model gives zero backward error. -/
theorem lsNormwiseBackwardErrorEtaF_eq_zero_of_isLeastSquaresMinimizer
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (hmin : IsLeastSquaresMinimizer A b y) :
    lsNormwiseBackwardErrorEtaF theta A b y = 0 := by
  apply le_antisymm
  · unfold lsNormwiseBackwardErrorEtaF
    exact csInf_le (lsNormwiseBackwardErrorValuesF.bddBelow theta A b y)
      (lsNormwiseBackwardErrorValuesF.zero_mem_of_isLeastSquaresMinimizer
        theta A b y hmin)
  · exact lsNormwiseBackwardErrorEtaF_nonneg theta A b y
/-- The (20.20) infimum model is no larger than any attainable perturbation
    cost. -/
theorem lsNormwiseBackwardErrorEtaF_le_of_mem {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorValuesF theta A b y) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤ eta := by
  unfold lsNormwiseBackwardErrorEtaF
  exact csInf_le (lsNormwiseBackwardErrorValuesF.bddBelow theta A b y) heta
/-- Higham, 2nd ed., Chapter 20, Theorem 20.5 discussion after (20.20):
    matrix-only attainable costs for the limiting `theta = infinity` convention,
    where right-hand-side perturbations are forbidden by setting
    `Delta b = 0`.  This records the body-text limiting model; it is not an
    end-of-chapter exercise statement. -/
noncomputable def lsNormwiseBackwardErrorMatrixOnlyValuesF {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ DeltaA : Fin m → Fin n → ℝ,
    LSNormwiseBackwardErrorFeasible A b y DeltaA (0 : Fin m → ℝ) ∧
      eta = frobNormRect DeltaA}
/-- Infimum model for the matrix-only limiting branch of (20.20), corresponding
    to the source convention `theta = infinity` and `Delta b = 0`. -/
noncomputable def lsNormwiseBackwardErrorMatrixOnlyEtaF {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (lsNormwiseBackwardErrorMatrixOnlyValuesF A b y)
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_of_feasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA (0 : Fin m → ℝ)) :
    frobNormRect DeltaA ∈
      lsNormwiseBackwardErrorMatrixOnlyValuesF A b y := by
  exact ⟨DeltaA, hfeas, rfl⟩
/-- Matrix-only attainable values are ordinary finite-`theta` attainable values
    for every finite weight, because the weighted block cost reduces to
    `||DeltaA||_F` when `Delta b = 0`. -/
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_valuesF {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) {eta : ℝ}
    (heta : eta ∈ lsNormwiseBackwardErrorMatrixOnlyValuesF A b y) :
    eta ∈ lsNormwiseBackwardErrorValuesF theta A b y := by
  rcases heta with ⟨DeltaA, hfeas, rfl⟩
  simpa [lsNormwiseBackwardErrorCostF_eq_frobNormRect_of_deltab_zero] using
    lsNormwiseBackwardErrorValuesF.mem_of_feasible theta A b y DeltaA
      (0 : Fin m → ℝ) hfeas
/-- The matrix-only limiting attainable-cost set is nonempty: choosing
    `DeltaA = -A` makes the perturbed matrix zero, so every candidate `y` is an
    exact least-squares minimizer for the unperturbed right-hand side. -/
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.nonempty {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    (lsNormwiseBackwardErrorMatrixOnlyValuesF A b y).Nonempty := by
  refine ⟨frobNormRect (fun i j => -A i j), ?_⟩
  apply lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_of_feasible
  intro z
  simp [lsObjective, lsResidual, rectMatMulVec, vecNorm2Sq]
/-- Matrix-only zero branch of the limiting `theta = infinity` model: if `y`
    is already an exact least-squares minimizer, then the zero matrix
    perturbation is attainable with `Delta b = 0`. -/
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.zero_mem_of_isLeastSquaresMinimizer
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (hmin : IsLeastSquaresMinimizer A b y) :
    (0 : ℝ) ∈ lsNormwiseBackwardErrorMatrixOnlyValuesF A b y := by
  have hmem :
      frobNormRect (0 : Fin m → Fin n → ℝ) ∈
        lsNormwiseBackwardErrorMatrixOnlyValuesF A b y :=
    lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_of_feasible A b y
      (0 : Fin m → Fin n → ℝ) (by
        simpa [LSNormwiseBackwardErrorFeasible] using hmin)
  simpa [frobNormRect, frobNormSqRect] using hmem
/-- The matrix-only limiting attainable-cost set is bounded below by zero. -/
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.bddBelow {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (lsNormwiseBackwardErrorMatrixOnlyValuesF A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, _hfeas, rfl⟩
  exact frobNormRect_nonneg DeltaA
theorem lsNormwiseBackwardErrorMatrixOnlyValuesF.nonneg_of_mem {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorMatrixOnlyValuesF A b y) :
    0 ≤ eta := by
  rcases heta with ⟨DeltaA, _hfeas, rfl⟩
  exact frobNormRect_nonneg DeltaA
/-- The matrix-only limiting infimum model is nonnegative. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ lsNormwiseBackwardErrorMatrixOnlyEtaF A b y := by
  unfold lsNormwiseBackwardErrorMatrixOnlyEtaF
  apply Real.sInf_nonneg
  intro eta heta
  exact lsNormwiseBackwardErrorMatrixOnlyValuesF.nonneg_of_mem A b y heta
/-- Matrix-only zero branch of the limiting `theta = infinity` model: exact
    least-squares minimizers have zero matrix-only backward error. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_eq_zero_of_isLeastSquaresMinimizer
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (hmin : IsLeastSquaresMinimizer A b y) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b y = 0 := by
  apply le_antisymm
  · unfold lsNormwiseBackwardErrorMatrixOnlyEtaF
    exact csInf_le
      (lsNormwiseBackwardErrorMatrixOnlyValuesF.bddBelow A b y)
      (lsNormwiseBackwardErrorMatrixOnlyValuesF.zero_mem_of_isLeastSquaresMinimizer
        A b y hmin)
  · exact lsNormwiseBackwardErrorMatrixOnlyEtaF_nonneg A b y
/-- The matrix-only limiting infimum is no larger than any matrix-only
    attainable perturbation norm. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_le_of_mem {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorMatrixOnlyValuesF A b y) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b y ≤ eta := by
  unfold lsNormwiseBackwardErrorMatrixOnlyEtaF
  exact csInf_le
    (lsNormwiseBackwardErrorMatrixOnlyValuesF.bddBelow A b y) heta
/-- Any matrix-only feasible perturbation gives an explicit upper bound for
    the limiting `theta = infinity` model. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_le_frobNorm_of_feasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA (0 : Fin m → ℝ)) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b y ≤ frobNormRect DeltaA :=
  lsNormwiseBackwardErrorMatrixOnlyEtaF_le_of_mem A b y
    (lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_of_feasible A b y DeltaA hfeas)
/-- Every matrix-only attainable value is an upper bound for the finite-`theta`
    `eta_F` infimum as well. -/
theorem lsNormwiseBackwardErrorEtaF_le_of_matrixOnly_mem {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorMatrixOnlyValuesF A b y) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤ eta :=
  lsNormwiseBackwardErrorEtaF_le_of_mem theta A b y
    (lsNormwiseBackwardErrorMatrixOnlyValuesF.mem_valuesF theta A b y heta)
/-- Finite-`theta` backward errors are bounded above by the matrix-only
    limiting model: every `Delta b = 0` perturbation allowed in the
    `theta = infinity` convention is also admissible for any finite weight. -/
theorem lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorMatrixOnlyEtaF A b y := by
  unfold lsNormwiseBackwardErrorMatrixOnlyEtaF
  apply le_csInf (lsNormwiseBackwardErrorMatrixOnlyValuesF.nonempty A b y)
  intro eta heta
  exact lsNormwiseBackwardErrorEtaF_le_of_matrixOnly_mem theta A b y heta
/-- Any feasible perturbation in (20.20) gives an explicit upper bound for the
    infimum model `eta_F(y)`. -/
theorem lsNormwiseBackwardErrorEtaF_le_costF_of_feasible {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  exact lsNormwiseBackwardErrorEtaF_le_of_mem theta A b y
    (lsNormwiseBackwardErrorValuesF.mem_of_feasible theta A b y
      DeltaA Deltab hfeas)
/-- Minimum-attainment handoff for Higham's normwise backward error (20.20).
    If a feasible perturbation has no larger cost than every other feasible
    perturbation, then the infimum model `eta_F(y)` equals its cost.  This is
    only an exact bridge for a future attainment proof, not the missing
    Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_eq_costF_of_feasible_minimizer
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab)
    (hmin : ∀ (DeltaA' : Fin m → Fin n → ℝ) (Deltab' : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA' Deltab' →
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
          lsNormwiseBackwardErrorCostF theta DeltaA' Deltab') :
    lsNormwiseBackwardErrorEtaF theta A b y =
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  apply le_antisymm
  · exact lsNormwiseBackwardErrorEtaF_le_costF_of_feasible
      theta A b y DeltaA Deltab hfeas
  · unfold lsNormwiseBackwardErrorEtaF
    apply le_csInf (lsNormwiseBackwardErrorValuesF.nonempty theta A b y)
    intro eta heta
    rcases heta with ⟨DeltaA', Deltab', hfeas', heta_eq⟩
    rw [heta_eq]
    exact hmin DeltaA' Deltab' hfeas'
/-- Exact-attainment consequence for (20.20): once a cost-minimizing feasible
    perturbation is supplied, `eta_F(y)` itself belongs to the attainable-cost
    set.  The existence of such a minimizer remains the open compactness/SVD
    foundation for Theorem 20.5. -/
theorem lsNormwiseBackwardErrorEtaF_mem_valuesF_of_exists_feasible_minimizer
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          ∀ (DeltaA' : Fin m → Fin n → ℝ) (Deltab' : Fin m → ℝ),
            LSNormwiseBackwardErrorFeasible A b y DeltaA' Deltab' →
              lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
                lsNormwiseBackwardErrorCostF theta DeltaA' Deltab') :
    lsNormwiseBackwardErrorEtaF theta A b y ∈
      lsNormwiseBackwardErrorValuesF theta A b y := by
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hmin⟩
  refine ⟨DeltaA, Deltab, hfeas, ?_⟩
  exact lsNormwiseBackwardErrorEtaF_eq_costF_of_feasible_minimizer
    theta A b y DeltaA Deltab hfeas hmin
/-- Exact perturbation witness form of the (20.20) attainment handoff. -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_of_exists_feasible_minimizer
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          ∀ (DeltaA' : Fin m → Fin n → ℝ) (Deltab' : Fin m → ℝ),
            LSNormwiseBackwardErrorFeasible A b y DeltaA' Deltab' →
              lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
                lsNormwiseBackwardErrorCostF theta DeltaA' Deltab') :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          lsNormwiseBackwardErrorEtaF theta A b y := by
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hmin⟩
  refine ⟨DeltaA, Deltab, hfeas, ?_⟩
  exact (lsNormwiseBackwardErrorEtaF_eq_costF_of_feasible_minimizer
    theta A b y DeltaA Deltab hfeas hmin).symm
/-- Closed-value-set bridge for Higham's normwise backward error (20.20).
    If the attainable weighted-cost set is closed, then the infimum model
    `eta_F(y)` is an actual least element of that set.  This is a compactness
    bridge for the later minimizer-existence proof, not the Walden--Karlson--Sun
    formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_isLeast_valuesF_of_isClosed_valuesF
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hclosed : IsClosed (lsNormwiseBackwardErrorValuesF theta A b y)) :
    IsLeast (lsNormwiseBackwardErrorValuesF theta A b y)
      (lsNormwiseBackwardErrorEtaF theta A b y) := by
  unfold lsNormwiseBackwardErrorEtaF
  exact hclosed.isLeast_csInf
    (lsNormwiseBackwardErrorValuesF.nonempty theta A b y)
    (lsNormwiseBackwardErrorValuesF.bddBelow theta A b y)
/-- Closed-value-set attainment for (20.20): closedness of the attainable-cost
    set upgrades the infimum model `eta_F(y)` to an attainable value. -/
theorem lsNormwiseBackwardErrorEtaF_mem_valuesF_of_isClosed_valuesF
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hclosed : IsClosed (lsNormwiseBackwardErrorValuesF theta A b y)) :
    lsNormwiseBackwardErrorEtaF theta A b y ∈
      lsNormwiseBackwardErrorValuesF theta A b y :=
  (lsNormwiseBackwardErrorEtaF_isLeast_valuesF_of_isClosed_valuesF
    theta A b y hclosed).1
/-- Feasible-witness form of the closed-value-set bridge for (20.20).  The
    remaining selected-scope work is proving the closedness/minimizer foundation
    and then the spectral formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_of_isClosed_valuesF
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hclosed : IsClosed (lsNormwiseBackwardErrorValuesF theta A b y)) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          lsNormwiseBackwardErrorEtaF theta A b y := by
  rcases lsNormwiseBackwardErrorEtaF_mem_valuesF_of_isClosed_valuesF
      theta A b y hclosed with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  exact ⟨DeltaA, Deltab, hfeas, heta_eq.symm⟩
/-- Minimum-attainment for the finite positive-`theta` normwise backward-error
    model (20.20).  The proof localizes the global infimum to one bounded
    attainable sublevel, uses compact-image closedness of that sublevel, and
    then identifies the bounded and global infima.  This proves existence of a
    source minimum for positive finite `theta`; it does not prove the
    Walden--Karlson--Sun SVD formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_isLeast_valuesF_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    IsLeast (lsNormwiseBackwardErrorValuesF theta A b y)
      (lsNormwiseBackwardErrorEtaF theta A b y) := by
  let values := lsNormwiseBackwardErrorValuesF theta A b y
  let eta0 := lsNormwiseBackwardErrorEtaF theta A b y
  rcases lsNormwiseBackwardErrorValuesF.nonempty theta A b y with ⟨R, hRmem⟩
  have hRnonneg : 0 ≤ R :=
    lsNormwiseBackwardErrorValuesF.nonneg_of_mem theta A b y hRmem
  let boundedValues : Set ℝ := values ∩ Set.Iic R
  have hclosed : IsClosed boundedValues := by
    simpa [values, boundedValues] using
      lsNormwiseBackwardErrorValuesF.sublevel_isClosed
        (m := m) (n := n) htheta hRnonneg A b y
  have hnonempty : boundedValues.Nonempty := ⟨R, hRmem, by simp⟩
  have hbdd : BddBelow boundedValues := by
    refine ⟨0, ?_⟩
    intro eta heta
    exact lsNormwiseBackwardErrorValuesF.nonneg_of_mem theta A b y
      (by simpa [values, boundedValues] using heta.1)
  have hsubset : boundedValues ⊆ values := by
    intro eta heta
    exact heta.1
  have hinf_ge : sInf values ≤ sInf boundedValues := by
    exact le_csInf hnonempty fun eta heta =>
      csInf_le (lsNormwiseBackwardErrorValuesF.bddBelow theta A b y)
        (hsubset heta)
  have hinf_le : sInf boundedValues ≤ sInf values := by
    refine le_of_forall_pos_le_add ?_
    intro eps heps
    by_cases hcase : sInf values + eps < R
    · rcases exists_lt_of_csInf_lt
        (lsNormwiseBackwardErrorValuesF.nonempty theta A b y)
        (lt_add_of_pos_right (sInf values) heps) with ⟨eta, heta, heta_lt⟩
      have heta_bounded : eta ∈ boundedValues := by
        refine ⟨by simpa [values] using heta, ?_⟩
        exact le_of_lt (lt_trans heta_lt hcase)
      exact (csInf_le hbdd heta_bounded).trans (le_of_lt heta_lt)
    · have htarget : R ≤ sInf values + eps := le_of_not_gt hcase
      exact (csInf_le hbdd ⟨hRmem, by simp⟩).trans htarget
  have hinf_eq : sInf boundedValues = sInf values := le_antisymm hinf_le hinf_ge
  have hleast_bounded : IsLeast boundedValues (sInf boundedValues) :=
    hclosed.isLeast_csInf hnonempty hbdd
  have heta_mem_bounded : eta0 ∈ boundedValues := by
    have hmem : sInf boundedValues ∈ boundedValues := hleast_bounded.1
    simpa [eta0, lsNormwiseBackwardErrorEtaF, values, hinf_eq] using hmem
  refine ⟨?_, ?_⟩
  · exact hsubset heta_mem_bounded
  · intro eta heta
    simpa [eta0] using
      lsNormwiseBackwardErrorEtaF_le_of_mem theta A b y
        (by simpa [values] using heta)
/-- Positive finite-`theta` attainment for (20.20): the infimum model
    `eta_F(y)` itself is an attainable weighted perturbation cost.  This is the
    minimum-existence part of Theorem 20.5's setup, before the formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_mem_valuesF_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEtaF theta A b y ∈
      lsNormwiseBackwardErrorValuesF theta A b y :=
  (lsNormwiseBackwardErrorEtaF_isLeast_valuesF_of_positive_theta
    htheta A b y).1
/-- Positive finite-`theta` feasible minimizer existence for (20.20): there is
    a feasible perturbation pair whose weighted Frobenius cost is no larger
    than the cost of any other feasible perturbation.  This is still prior to
    the Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_minimizer_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        ∀ (DeltaA' : Fin m → Fin n → ℝ) (Deltab' : Fin m → ℝ),
          LSNormwiseBackwardErrorFeasible A b y DeltaA' Deltab' →
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
              lsNormwiseBackwardErrorCostF theta DeltaA' Deltab' := by
  rcases lsNormwiseBackwardErrorEtaF_mem_valuesF_of_positive_theta
      htheta A b y with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  refine ⟨DeltaA, Deltab, hfeas, ?_⟩
  intro DeltaA' Deltab' hfeas'
  rw [← heta_eq]
  exact lsNormwiseBackwardErrorEtaF_le_costF_of_feasible
    theta A b y DeltaA' Deltab' hfeas'
/-- Positive finite-`theta` witness form of minimum-attainment for (20.20):
    there is a feasible perturbation pair whose cost is exactly `eta_F(y)`.
    The spectral expression (20.21) remains a separate theorem. -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          lsNormwiseBackwardErrorEtaF theta A b y := by
  rcases lsNormwiseBackwardErrorEtaF_mem_valuesF_of_positive_theta
      htheta A b y with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  exact ⟨DeltaA, Deltab, hfeas, heta_eq.symm⟩
/-- Matrix-only limiting dependency for (20.20): any exact finite-`theta`
    minimizer has right-hand-side perturbation norm bounded by the
    matrix-only infimum divided by `theta`.  This makes the source's
    "large `theta` forces `Delta b` to zero" compactness route explicit. -/
theorem lsNormwiseBackwardErrorEtaF_minimizer_deltab_norm_le_matrixOnlyEtaF_div_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hcost :
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
        lsNormwiseBackwardErrorEtaF theta A b y) :
    vecNorm2 Deltab ≤ lsNormwiseBackwardErrorMatrixOnlyEtaF A b y / theta := by
  have hweighted :
      theta * vecNorm2 Deltab ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_weighted_deltab_le
      (le_of_lt htheta) DeltaA Deltab
  have heta_le :
      lsNormwiseBackwardErrorEtaF theta A b y ≤
        lsNormwiseBackwardErrorMatrixOnlyEtaF A b y :=
    lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF theta A b y
  rw [le_div_iff₀ htheta]
  calc
    vecNorm2 Deltab * theta = theta * vecNorm2 Deltab := by ring
    _ ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab := hweighted
    _ = lsNormwiseBackwardErrorEtaF theta A b y := hcost
    _ ≤ lsNormwiseBackwardErrorMatrixOnlyEtaF A b y := heta_le
/-- Existence form of the finite-`theta` minimizer RHS bound: for every
    positive finite source weight, there is an exact minimizing perturbation
    pair whose `Delta b` component is bounded by the matrix-only infimum divided
    by `theta`. -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_deltab_norm_le_matrixOnlyEtaF_div_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          lsNormwiseBackwardErrorEtaF theta A b y ∧
        vecNorm2 Deltab ≤
          lsNormwiseBackwardErrorMatrixOnlyEtaF A b y / theta := by
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_of_positive_theta
      htheta A b y with ⟨DeltaA, Deltab, hfeas, hcost⟩
  exact ⟨DeltaA, Deltab, hfeas, hcost,
    lsNormwiseBackwardErrorEtaF_minimizer_deltab_norm_le_matrixOnlyEtaF_div_theta
      htheta A b y DeltaA Deltab hcost⟩
/-- Eventual RHS-vanishing form of the finite-minimizer bound: for every
    positive tolerance, all sufficiently large finite weights allow an exact
    minimizing perturbation pair with `||Delta b||_2` below that tolerance. -/
theorem lsNormwiseBackwardErrorEtaF_eventually_exists_feasible_cost_eq_deltab_norm_lt_atTop
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ theta : ℝ in Filter.atTop,
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        0 < theta ∧
          LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            lsNormwiseBackwardErrorEtaF theta A b y ∧
          vecNorm2 Deltab < eps := by
  let M := lsNormwiseBackwardErrorMatrixOnlyEtaF A b y
  filter_upwards [Filter.eventually_gt_atTop (max 0 (M / eps))] with theta htheta
  have htheta_pos : 0 < theta :=
    lt_of_le_of_lt (le_max_left (0 : ℝ) (M / eps)) htheta
  have hM_div_lt : M / eps < theta :=
    lt_of_le_of_lt (le_max_right (0 : ℝ) (M / eps)) htheta
  have hM_lt : M < eps * theta := by
    have hraw : M < theta * eps := (div_lt_iff₀ heps).mp hM_div_lt
    simpa [mul_comm] using hraw
  have hdiv_lt : M / theta < eps := by
    exact (div_lt_iff₀ htheta_pos).mpr hM_lt
  rcases
    lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_deltab_norm_le_matrixOnlyEtaF_div_theta
      htheta_pos A b y with
    ⟨DeltaA, Deltab, hfeas, hcost, hDeltab⟩
  exact ⟨DeltaA, Deltab, htheta_pos, hfeas, hcost,
    lt_of_le_of_lt hDeltab (by simpa [M] using hdiv_lt)⟩
/-- Finite positive-`theta` zero-backward-error characterization for (20.20):
    after minimum-attainment is available, `eta_F(y) = 0` exactly when `y` is
    already an exact least-squares minimizer for the unperturbed data.  This is
    a consistency bridge for the normwise backward-error model, not the
    Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_eq_zero_iff_isLeastSquaresMinimizer_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEtaF theta A b y = 0 ↔
      IsLeastSquaresMinimizer A b y := by
  constructor
  · intro heta
    have hmem :=
      lsNormwiseBackwardErrorEtaF_mem_valuesF_of_positive_theta htheta A b y
    have hzero_mem : (0 : ℝ) ∈
        lsNormwiseBackwardErrorValuesF theta A b y := by
      simpa [heta] using hmem
    exact
      (lsNormwiseBackwardErrorValuesF.zero_mem_iff_isLeastSquaresMinimizer
        (m := m) (n := n) (theta := theta) (ne_of_gt htheta) A b y).mp hzero_mem
  · intro hmin
    exact lsNormwiseBackwardErrorEtaF_eq_zero_of_isLeastSquaresMinimizer
      theta A b y hmin
/-- Finite positive-`theta` positive-backward-error characterization for
    (20.20): `eta_F(y)` is strictly positive exactly when `y` is not an exact
    least-squares minimizer of the original data. -/
theorem lsNormwiseBackwardErrorEtaF_pos_iff_not_isLeastSquaresMinimizer_of_positive_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 < lsNormwiseBackwardErrorEtaF theta A b y ↔
      ¬ IsLeastSquaresMinimizer A b y := by
  constructor
  · intro hpos hmin
    have hzero := lsNormwiseBackwardErrorEtaF_eq_zero_of_isLeastSquaresMinimizer
      theta A b y hmin
    linarith
  · intro hnot
    have hnonneg := lsNormwiseBackwardErrorEtaF_nonneg theta A b y
    have hne : lsNormwiseBackwardErrorEtaF theta A b y ≠ 0 := by
      intro hzero
      exact hnot
        ((lsNormwiseBackwardErrorEtaF_eq_zero_iff_isLeastSquaresMinimizer_of_positive_theta
          htheta A b y).mp hzero)
    exact lt_of_le_of_ne' hnonneg hne
/-- Monotonicity of the (20.20) infimum model in the source weight: increasing
    a nonnegative `theta` cannot decrease the best attainable weighted
    Frobenius perturbation cost. -/
theorem lsNormwiseBackwardErrorEtaF_mono_theta_nonneg {m n : ℕ}
    {theta1 theta2 : ℝ} (htheta1 : 0 ≤ theta1) (htheta12 : theta1 ≤ theta2)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEtaF theta1 A b y ≤
      lsNormwiseBackwardErrorEtaF theta2 A b y := by
  unfold lsNormwiseBackwardErrorEtaF
  apply le_csInf (lsNormwiseBackwardErrorValuesF.nonempty theta2 A b y)
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  rw [heta_eq]
  exact
    (lsNormwiseBackwardErrorEtaF_le_costF_of_feasible theta1 A b y
      DeltaA Deltab hfeas).trans
      (lsNormwiseBackwardErrorCostF_mono_theta_nonneg htheta1 htheta12
        DeltaA Deltab)
/-- Natural-grid limiting foundation for the finite-weight model in (20.20):
    the nondecreasing sequence `eta_F(k,y)` converges to the supremum of its
    finite-weight values.  This is a one-dimensional monotone-convergence
    statement, not the full `theta = infinity` WKS formula. -/
theorem lsNormwiseBackwardErrorEtaF_nat_tendsto_iSup {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Filter.Tendsto
      (fun k : ℕ => lsNormwiseBackwardErrorEtaF (k : ℝ) A b y)
      Filter.atTop
      (nhds (⨆ k : ℕ, lsNormwiseBackwardErrorEtaF (k : ℝ) A b y)) := by
  have hmono :
      Monotone (fun k : ℕ => lsNormwiseBackwardErrorEtaF (k : ℝ) A b y) := by
    intro k l hkl
    exact lsNormwiseBackwardErrorEtaF_mono_theta_nonneg
      (Nat.cast_nonneg k) (Nat.cast_le.mpr hkl) A b y
  have hbdd :
      BddAbove (Set.range
        (fun k : ℕ => lsNormwiseBackwardErrorEtaF (k : ℝ) A b y)) := by
    refine ⟨lsNormwiseBackwardErrorMatrixOnlyEtaF A b y, ?_⟩
    rintro eta ⟨k, rfl⟩
    exact lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF (k : ℝ) A b y
  exact tendsto_atTop_ciSup hmono hbdd
/-- The natural-grid finite-weight limit supremum is bounded above by the
    matrix-only limiting infimum.  This records the expected one-sided
    comparison between the finite weighted model and the `Delta b = 0` model. -/
theorem lsNormwiseBackwardErrorEtaF_nat_iSup_le_matrixOnlyEtaF {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    (⨆ k : ℕ, lsNormwiseBackwardErrorEtaF (k : ℝ) A b y) ≤
      lsNormwiseBackwardErrorMatrixOnlyEtaF A b y := by
  exact ciSup_le fun k =>
    lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF (k : ℝ) A b y
/-- Nonnegative-weight limiting foundation for the finite-weight model in
    (20.20): along the ordered subtype of nonnegative real weights, `eta_F`
    converges to the supremum of its finite nonnegative values. -/
theorem lsNormwiseBackwardErrorEtaF_nonneg_tendsto_iSup {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Filter.Tendsto
      (fun theta : {theta : ℝ // 0 ≤ theta} =>
        lsNormwiseBackwardErrorEtaF theta.1 A b y)
      Filter.atTop
      (nhds (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y)) := by
  have hmono :
      Monotone (fun theta : {theta : ℝ // 0 ≤ theta} =>
        lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
    intro theta1 theta2 htheta
    exact lsNormwiseBackwardErrorEtaF_mono_theta_nonneg
      theta1.2 htheta A b y
  have hbdd :
      BddAbove (Set.range
        (fun theta : {theta : ℝ // 0 ≤ theta} =>
          lsNormwiseBackwardErrorEtaF theta.1 A b y)) := by
    refine ⟨lsNormwiseBackwardErrorMatrixOnlyEtaF A b y, ?_⟩
    rintro eta ⟨theta, rfl⟩
    exact lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF theta.1 A b y
  exact tendsto_atTop_ciSup hmono hbdd
/-- The supremum of the finite nonnegative-weight `eta_F` values is bounded
    above by the matrix-only limiting infimum. -/
theorem lsNormwiseBackwardErrorEtaF_nonneg_iSup_le_matrixOnlyEtaF {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y) ≤
      lsNormwiseBackwardErrorMatrixOnlyEtaF A b y := by
  exact ciSup_le fun theta =>
    lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF theta.1 A b y
/-- Each finite nonnegative weighted backward error is bounded by the
    nonnegative-weight supremum appearing in the `theta -> infinity` limiting
    foundation for (20.20). -/
theorem lsNormwiseBackwardErrorEtaF_le_nonneg_iSup_of_nonneg {m n : ℕ}
    {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤
      (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
  have hbdd :
      BddAbove (Set.range
        (fun theta : {theta : ℝ // 0 ≤ theta} =>
          lsNormwiseBackwardErrorEtaF theta.1 A b y)) := by
    refine ⟨lsNormwiseBackwardErrorMatrixOnlyEtaF A b y, ?_⟩
    rintro eta ⟨theta, rfl⟩
    exact lsNormwiseBackwardErrorEtaF_le_matrixOnlyEtaF theta.1 A b y
  exact le_ciSup
    (f := fun theta : {theta : ℝ // 0 ≤ theta} =>
      lsNormwiseBackwardErrorEtaF theta.1 A b y)
    hbdd ⟨theta, htheta⟩
/-- Compactness-route sublevel bound for (20.20): an exact finite minimizer
    at any weight `theta >= 1` has its weight-one Frobenius cost bounded by the
    nonnegative finite-weight supremum, the limit already proved for
    `theta -> infinity`. -/
theorem lsNormwiseBackwardErrorEtaF_minimizer_costF_one_le_nonneg_iSup_of_one_le_theta
    {m n : ℕ} {theta : ℝ} (hone : 1 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hcost :
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
        lsNormwiseBackwardErrorEtaF theta A b y) :
    lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤
      (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
  have hmono :
      lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_mono_theta_nonneg
      (by norm_num : (0 : ℝ) ≤ 1) hone DeltaA Deltab
  have htheta_nonneg : 0 ≤ theta := le_trans zero_le_one hone
  have heta_le :
      lsNormwiseBackwardErrorEtaF theta A b y ≤
        (⨆ theta : {theta : ℝ // 0 ≤ theta},
          lsNormwiseBackwardErrorEtaF theta.1 A b y) :=
    lsNormwiseBackwardErrorEtaF_le_nonneg_iSup_of_nonneg
      htheta_nonneg A b y
  calc
    lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab := hmono
    _ = lsNormwiseBackwardErrorEtaF theta A b y := hcost
    _ ≤ (⨆ theta : {theta : ℝ // 0 ≤ theta},
          lsNormwiseBackwardErrorEtaF theta.1 A b y) := heta_le
/-- Existence form of the fixed-sublevel bound: for every finite weight
    `theta >= 1`, an exact minimizer can be chosen whose weight-one cost is
    bounded by the nonnegative finite-weight supremum. -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_costF_one_le_nonneg_iSup_of_one_le_theta
    {m n : ℕ} {theta : ℝ} (hone : 1 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          lsNormwiseBackwardErrorEtaF theta A b y ∧
        lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤
          (⨆ theta : {theta : ℝ // 0 ≤ theta},
            lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
  have htheta_pos : 0 < theta := lt_of_lt_of_le zero_lt_one hone
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_of_positive_theta
      htheta_pos A b y with ⟨DeltaA, Deltab, hfeas, hcost⟩
  exact ⟨DeltaA, Deltab, hfeas, hcost,
    lsNormwiseBackwardErrorEtaF_minimizer_costF_one_le_nonneg_iSup_of_one_le_theta
      hone A b y DeltaA Deltab hcost⟩
/-- Eventual compactness-route package for the `theta = infinity` discussion:
    for every positive tolerance and all sufficiently large finite weights,
    there is an exact minimizer whose weight-one cost is bounded by the proved
    nonnegative finite-weight limit supremum and whose right-hand-side
    perturbation is below the tolerance. -/
theorem lsNormwiseBackwardErrorEtaF_eventually_exists_feasible_cost_eq_costF_one_le_nonneg_iSup_deltab_norm_lt_atTop
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ theta : ℝ in Filter.atTop,
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        1 ≤ theta ∧
          0 < theta ∧
          LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            lsNormwiseBackwardErrorEtaF theta A b y ∧
          lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤
            (⨆ theta : {theta : ℝ // 0 ≤ theta},
              lsNormwiseBackwardErrorEtaF theta.1 A b y) ∧
          vecNorm2 Deltab < eps := by
  filter_upwards
    [Filter.eventually_ge_atTop (1 : ℝ),
      lsNormwiseBackwardErrorEtaF_eventually_exists_feasible_cost_eq_deltab_norm_lt_atTop
        A b y heps] with theta hone htheta_pack
  rcases htheta_pack with ⟨DeltaA, Deltab, htheta_pos, hfeas, hcost, hdeltab⟩
  exact ⟨DeltaA, Deltab, hone, htheta_pos, hfeas, hcost,
    lsNormwiseBackwardErrorEtaF_minimizer_costF_one_le_nonneg_iSup_of_one_le_theta
      hone A b y DeltaA Deltab hcost,
    hdeltab⟩
/-- Reverse limiting inequality for the matrix-only convention in (20.20):
    the matrix-only `Delta b = 0` infimum is bounded by the supremum of the
    finite nonnegative weighted backward errors.  The proof extracts a
    convergent subsequence of exact finite minimizers from the fixed weight-one
    compact sublevel and uses the `Delta b -> 0` bound to obtain a matrix-only
    feasible limit point. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_le_nonneg_iSup {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b y ≤
      (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
  let L : ℝ :=
    (⨆ theta : {theta : ℝ // 0 ≤ theta},
      lsNormwiseBackwardErrorEtaF theta.1 A b y)
  let M : ℝ := lsNormwiseBackwardErrorMatrixOnlyEtaF A b y
  have hL_nonneg : 0 ≤ L := by
    have h0_nonneg :
        0 ≤ lsNormwiseBackwardErrorEtaF (0 : ℝ) A b y :=
      lsNormwiseBackwardErrorEtaF_nonneg (0 : ℝ) A b y
    have h0_le :
        lsNormwiseBackwardErrorEtaF (0 : ℝ) A b y ≤ L := by
      simpa [L] using
        (lsNormwiseBackwardErrorEtaF_le_nonneg_iSup_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 0) A b y)
    exact h0_nonneg.trans h0_le
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using lsNormwiseBackwardErrorMatrixOnlyEtaF_nonneg A b y
  have hexists : ∀ k : ℕ,
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF (((k + 1 : ℕ) : ℝ)) DeltaA Deltab =
            lsNormwiseBackwardErrorEtaF (((k + 1 : ℕ) : ℝ)) A b y ∧
          lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤ L ∧
          vecNorm2 Deltab ≤ M / (((k + 1 : ℕ) : ℝ)) := by
    intro k
    let theta : ℝ := ((k + 1 : ℕ) : ℝ)
    have htheta_pos : 0 < theta := by
      have h : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos k
      simpa [theta] using h
    have hone : 1 ≤ theta := by
      have h : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      simp [theta] at h ⊢
    rcases
      lsNormwiseBackwardErrorEtaF_exists_feasible_cost_eq_deltab_norm_le_matrixOnlyEtaF_div_theta
        htheta_pos A b y with
      ⟨DeltaA, Deltab, hfeas, hcost, hdeltab⟩
    have hcost_one :
        lsNormwiseBackwardErrorCostF (1 : ℝ) DeltaA Deltab ≤ L := by
      simpa [L] using
        (lsNormwiseBackwardErrorEtaF_minimizer_costF_one_le_nonneg_iSup_of_one_le_theta
          hone A b y DeltaA Deltab hcost)
    exact ⟨DeltaA, Deltab, hfeas, by simpa [theta] using hcost,
      hcost_one, by simpa [M, theta] using hdeltab⟩
  choose DeltaA Deltab hfeas hcost hcost_one hdeltab using hexists
  let pseq : ℕ → (Fin m → Fin n → ℝ) × (Fin m → ℝ) :=
    fun k => (DeltaA k, Deltab k)
  let K : Set ((Fin m → Fin n → ℝ) × (Fin m → ℝ)) :=
    {p | LSNormwiseBackwardErrorFeasible A b y p.1 p.2 ∧
      lsNormwiseBackwardErrorCostF (1 : ℝ) p.1 p.2 ≤ L}
  have hKcompact : IsCompact K := by
    simpa [K, L] using
      LSNormwiseBackwardErrorFeasible.cost_sublevel_isCompact
        (m := m) (n := n) (theta := (1 : ℝ)) (R := L)
        (by norm_num : (0 : ℝ) < 1) hL_nonneg A b y
  have hpseq_mem : ∀ k, pseq k ∈ K := by
    intro k
    exact ⟨hfeas k, hcost_one k⟩
  rcases hKcompact.tendsto_subseq hpseq_mem with
    ⟨p, hpK, phi, hphi_mono, hp_tendsto⟩
  have hphi_atTop : Filter.Tendsto phi Filter.atTop Filter.atTop :=
    hphi_mono.tendsto_atTop
  have htheta_nat :
      Filter.Tendsto (fun k : ℕ => phi k + 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hphi_atTop
  have htheta_real :
      Filter.Tendsto
        (fun k : ℕ => (((phi k + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp htheta_nat
  have hbound_tendsto :
      Filter.Tendsto
        (fun k : ℕ => M / (((phi k + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop htheta_real
  have hdeltab_norm_tendsto_zero :
      Filter.Tendsto
        (fun k : ℕ => vecNorm2 (Deltab (phi k)))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero ?hnonneg ?hupper hbound_tendsto
    · intro k
      exact vecNorm2_nonneg (Deltab (phi k))
    · intro k
      exact hdeltab (phi k)
  have hdeltab_tendsto :
      Filter.Tendsto (fun k : ℕ => Deltab (phi k))
        Filter.atTop (nhds p.2) := by
    simpa [pseq, Function.comp_def] using
      (continuous_snd.tendsto p).comp hp_tendsto
  have hnorm_tendsto :
      Filter.Tendsto
        (fun k : ℕ => vecNorm2 (Deltab (phi k)))
        Filter.atTop (nhds (vecNorm2 p.2)) :=
    (continuous_vecNorm2.tendsto p.2).comp hdeltab_tendsto
  have hp2_norm_zero : vecNorm2 p.2 = 0 :=
    tendsto_nhds_unique hnorm_tendsto hdeltab_norm_tendsto_zero
  have hp2_zero : p.2 = 0 := by
    ext i
    exact (vecNorm2_eq_zero_iff p.2).mp hp2_norm_zero i
  have hmatrix_feas :
      LSNormwiseBackwardErrorFeasible A b y p.1 (0 : Fin m → ℝ) := by
    simpa [hp2_zero] using hpK.1
  have hfrob_le : frobNormRect p.1 ≤ L := by
    simpa [hp2_zero, lsNormwiseBackwardErrorCostF_eq_frobNormRect_of_deltab_zero]
      using hpK.2
  exact
    (lsNormwiseBackwardErrorMatrixOnlyEtaF_le_frobNorm_of_feasible
      A b y p.1 hmatrix_feas).trans (by simpa [L] using hfrob_le)
/-- The `theta = infinity` matrix-only model for (20.20) is exactly the
    supremum of the finite nonnegative weighted backward errors. -/
theorem lsNormwiseBackwardErrorMatrixOnlyEtaF_eq_nonneg_iSup {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b y =
      (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y) := by
  exact le_antisymm
    (lsNormwiseBackwardErrorMatrixOnlyEtaF_le_nonneg_iSup A b y)
    (lsNormwiseBackwardErrorEtaF_nonneg_iSup_le_matrixOnlyEtaF A b y)
/-- Real-parameter limiting foundation for (20.20): as `theta -> +∞`, the
    finite-weight backward error converges to the supremum of its nonnegative
    finite-weight values.  The source's full matrix-only formula still
    requires the reverse comparison with the `Delta b = 0` infimum. -/
theorem lsNormwiseBackwardErrorEtaF_tendsto_nonneg_iSup_atTop {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Filter.Tendsto
      (fun theta : ℝ => lsNormwiseBackwardErrorEtaF theta A b y)
      Filter.atTop
      (nhds (⨆ theta : {theta : ℝ // 0 ≤ theta},
        lsNormwiseBackwardErrorEtaF theta.1 A b y)) := by
  let clamp : ℝ → {theta : ℝ // 0 ≤ theta} :=
    fun theta => ⟨max theta 0, le_max_right theta 0⟩
  have hclamp : Filter.Tendsto clamp Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro bound
    refine ⟨bound.1, ?_⟩
    intro theta htheta
    change bound.1 ≤ max theta 0
    exact le_trans htheta (le_max_left theta 0)
  have hcomp :
      Filter.Tendsto
        (fun theta : ℝ =>
          lsNormwiseBackwardErrorEtaF (max theta 0) A b y)
        Filter.atTop
        (nhds (⨆ theta : {theta : ℝ // 0 ≤ theta},
          lsNormwiseBackwardErrorEtaF theta.1 A b y)) := by
    simpa [clamp, Function.comp_def] using
      (lsNormwiseBackwardErrorEtaF_nonneg_tendsto_iSup A b y).comp hclamp
  exact Filter.Tendsto.congr'
    (f₁ := fun theta : ℝ =>
      lsNormwiseBackwardErrorEtaF (max theta 0) A b y)
    (f₂ := fun theta : ℝ => lsNormwiseBackwardErrorEtaF theta A b y)
    (by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with theta htheta
      simp [max_eq_left htheta])
    hcomp
/-- Matrix-only limiting form of (20.20): as `theta -> +∞`, the finite-weight
    normwise backward error converges to the matrix-only `Delta b = 0`
    infimum. -/
theorem lsNormwiseBackwardErrorEtaF_tendsto_matrixOnlyEtaF_atTop {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Filter.Tendsto
      (fun theta : ℝ => lsNormwiseBackwardErrorEtaF theta A b y)
      Filter.atTop
      (nhds (lsNormwiseBackwardErrorMatrixOnlyEtaF A b y)) := by
  rw [lsNormwiseBackwardErrorMatrixOnlyEtaF_eq_nonneg_iSup A b y]
  exact lsNormwiseBackwardErrorEtaF_tendsto_nonneg_iSup_atTop A b y
/-- A bounded feasible perturbation cost in (20.20) bounds the infimum model
    `eta_F(y)`. -/
theorem lsNormwiseBackwardErrorEtaF_le_of_feasible_cost_le {m n : ℕ}
    (theta c : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab)
    (hcost : lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤ c) :
    lsNormwiseBackwardErrorEtaF theta A b y ≤ c :=
  (lsNormwiseBackwardErrorEtaF_le_costF_of_feasible theta A b y
    DeltaA Deltab hfeas).trans hcost
/-- Infimum-approximation form of Higham's definition (20.20): although the
    local model deliberately records `eta_F(y)` as an infimum rather than the
    source's printed minimum, every positive tolerance is attained up to that
    tolerance by an actual feasible perturbation.  This does not prove the
    missing minimum-attainment or the Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_cost_lt_add_eps {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorEtaF theta A b y ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab <
          lsNormwiseBackwardErrorEtaF theta A b y + eps := by
  let values := lsNormwiseBackwardErrorValuesF theta A b y
  have hlt : sInf values < sInf values + eps :=
    lt_add_of_pos_right (sInf values) heps
  rcases exists_lt_of_csInf_lt
      (lsNormwiseBackwardErrorValuesF.nonempty theta A b y) hlt with
    ⟨eta, heta, heta_lt⟩
  rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  refine ⟨DeltaA, Deltab, hfeas, ?_, ?_⟩
  · exact lsNormwiseBackwardErrorEtaF_le_of_mem theta A b y
      (by simpa [values] using
        (lsNormwiseBackwardErrorValuesF.mem_of_feasible theta A b y
          DeltaA Deltab hfeas))
  · simpa [values, lsNormwiseBackwardErrorEtaF, heta_eq] using heta_lt
/-- Epsilon-near form of (20.20) for the matrix perturbation: every positive
    tolerance admits an actual feasible perturbation whose `DeltaA` Frobenius
    norm is below `eta_F(y) + eps`.  This remains an infimum result, not the
    missing minimum-attainment or the Walden--Karlson--Sun formula (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_deltaA_norm_lt_add_eps
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorEtaF theta A b y ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab <
          lsNormwiseBackwardErrorEtaF theta A b y + eps ∧
        frobNormRect DeltaA <
          lsNormwiseBackwardErrorEtaF theta A b y + eps := by
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_cost_lt_add_eps
      theta A b y heps with ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt⟩
  have hDeltaA_le :
      frobNormRect DeltaA ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_deltaA_le theta DeltaA Deltab
  exact ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt,
    lt_of_le_of_lt hDeltaA_le hcost_lt⟩
/-- Finite positive-`theta` consequence of the (20.20) infimum model and the
    discussion following it: every positive tolerance admits an actual feasible
    perturbation with cost within that tolerance of `eta_F(y)`, and its
    right-hand-side perturbation is bounded by `(eta_F(y) + eps) / theta`.
    This is an epsilon form of the source's statement that large `theta`
    forces `Delta b` toward zero; it is not the missing `theta = ∞` formula. -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_deltab_norm_lt_add_eps_div_theta
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorEtaF theta A b y ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab <
          lsNormwiseBackwardErrorEtaF theta A b y + eps ∧
        vecNorm2 Deltab <
          (lsNormwiseBackwardErrorEtaF theta A b y + eps) / theta := by
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_cost_lt_add_eps
      theta A b y heps with ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt⟩
  have hweighted :
      theta * vecNorm2 Deltab ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_weighted_deltab_le
      (le_of_lt htheta) DeltaA Deltab
  have htheta_norm_lt :
      theta * vecNorm2 Deltab <
        lsNormwiseBackwardErrorEtaF theta A b y + eps :=
    lt_of_le_of_lt hweighted hcost_lt
  refine ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt, ?_⟩
  rw [lt_div_iff₀ htheta]
  simpa [mul_comm] using htheta_norm_lt
/-- Pointwise coercivity form of the (20.20) infimum model: for positive
    finite `theta`, every tolerance admits a feasible perturbation whose cost
    is within that tolerance of `eta_F(y)` and whose individual entries are
    bounded by the same finite radius.  This is a compactness/coercivity
    ingredient for proving minimum-attainment, not the spectral formula
    (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_entry_bounds_lt_add_eps
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorEtaF theta A b y ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab <
          lsNormwiseBackwardErrorEtaF theta A b y + eps ∧
        (∀ i j, |DeltaA i j| <
          lsNormwiseBackwardErrorEtaF theta A b y + eps) ∧
        (∀ i, |Deltab i| <
          (lsNormwiseBackwardErrorEtaF theta A b y + eps) / theta) := by
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_cost_lt_add_eps
      theta A b y heps with ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt⟩
  refine ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt, ?_, ?_⟩
  · intro i j
    exact lt_of_le_of_lt
      (lsNormwiseBackwardErrorCostF_deltaA_entry_abs_le theta DeltaA Deltab i j)
      hcost_lt
  · intro i
    have hweighted :
        theta * |Deltab i| ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
      lsNormwiseBackwardErrorCostF_weighted_deltab_entry_abs_le
        (le_of_lt htheta) DeltaA Deltab i
    have htheta_abs_lt :
        theta * |Deltab i| <
          lsNormwiseBackwardErrorEtaF theta A b y + eps :=
      lt_of_le_of_lt hweighted hcost_lt
    rw [lt_div_iff₀ htheta]
    simpa [mul_comm] using htheta_abs_lt
/-- Radius form of the epsilon-near coercivity result for (20.20): every
    radius strictly above the infimum model `eta_F(y)` contains an actual
    feasible perturbation cost, and for positive finite `theta` the witness has
    entrywise perturbation bounds by that radius.  This is still a
    compactness ingredient, not minimum-attainment or the spectral formula
    (20.21). -/
theorem lsNormwiseBackwardErrorEtaF_exists_feasible_entry_bounds_lt_radius
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {R : ℝ} (hR : lsNormwiseBackwardErrorEtaF theta A b y < R) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorEtaF theta A b y ≤
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab < R ∧
        (∀ i j, |DeltaA i j| < R) ∧
        (∀ i, |Deltab i| < R / theta) := by
  have heps : 0 < R - lsNormwiseBackwardErrorEtaF theta A b y :=
    sub_pos.mpr hR
  rcases lsNormwiseBackwardErrorEtaF_exists_feasible_entry_bounds_lt_add_eps
      htheta A b y heps with
    ⟨DeltaA, Deltab, hfeas, heta_le, hcost_lt, hDeltaA, hDeltab⟩
  have htarget :
      lsNormwiseBackwardErrorEtaF theta A b y +
          (R - lsNormwiseBackwardErrorEtaF theta A b y) = R := by
    ring
  refine ⟨DeltaA, Deltab, hfeas, heta_le, ?_, ?_, ?_⟩
  · simpa [htarget] using hcost_lt
  · intro i j
    simpa [htarget] using hDeltaA i j
  · intro i
    simpa [htarget] using hDeltab i
/-- Bounded-sublevel coercivity for the (20.20) attainable-cost set: for positive
    finite `theta`, any attainable cost below a radius `R` has a feasible
    perturbation witness whose individual matrix and right-hand-side entries are
    bounded by the corresponding finite radii. This is a compactness ingredient,
    not the closedness proof or the spectral formula (20.21). -/
theorem lsNormwiseBackwardErrorValuesF.exists_feasible_entry_bounds_of_mem_le
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta R : ℝ} (heta : eta ∈ lsNormwiseBackwardErrorValuesF theta A b y)
    (heta_le : eta ≤ R) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab = eta ∧
        (∀ i j, |DeltaA i j| ≤ R) ∧
        (∀ i, |Deltab i| ≤ R / theta) := by
  rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  have hcost_le_R :
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤ R := by
    simpa [heta_eq] using heta_le
  refine ⟨DeltaA, Deltab, hfeas, heta_eq.symm, ?_, ?_⟩
  · intro i j
    exact
      (lsNormwiseBackwardErrorCostF_deltaA_entry_abs_le
        theta DeltaA Deltab i j).trans hcost_le_R
  · intro i
    exact
      (lsNormwiseBackwardErrorCostF_deltab_entry_abs_le_cost_div_theta
        htheta DeltaA Deltab i).trans
        (div_le_div_of_nonneg_right hcost_le_R (le_of_lt htheta))
/-- Sublevel form of the bounded-entry witness for (20.20): a value in the
    finite-radius attainable-cost sublevel has a feasible perturbation witness
    with all entries bounded by the corresponding finite radii. -/
theorem lsNormwiseBackwardErrorValuesF.exists_feasible_entry_bounds_of_mem_sublevel
    {m n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    {eta R : ℝ}
    (heta : eta ∈ lsNormwiseBackwardErrorValuesF theta A b y ∩ Set.Iic R) :
    ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
      LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab = eta ∧
        (∀ i j, |DeltaA i j| ≤ R) ∧
        (∀ i, |Deltab i| ≤ R / theta) := by
  exact
    lsNormwiseBackwardErrorValuesF.exists_feasible_entry_bounds_of_mem_le
      htheta A b y heta.1 heta.2
/-- Squared scalar form of the WKS quantity
    `phi = sqrt(mu) ||r||_2 / ||y||_2`. -/
theorem lsNormwiseBackwardErrorPhi_sq_eq_mu_mul_residual_sq_div_y_sq
    {m n : ℕ} (theta : ℝ) (r : Fin m → ℝ)
    (y : Fin n → ℝ) :
    (lsNormwiseBackwardErrorPhi theta r y) ^ 2 =
      lsNormwiseBackwardErrorMu theta y * vecNorm2Sq r / vecNorm2Sq y := by
  unfold lsNormwiseBackwardErrorPhi
  rw [div_pow, mul_pow, Real.sq_sqrt (lsNormwiseBackwardErrorMu_nonneg theta y),
    vecNorm2_sq r, vecNorm2_sq y]
/-- The Theorem 20.5 eigenmatrix is symmetric in the repository's finite-matrix
    predicate form. -/
theorem lsNormwiseBackwardErrorEigenMatrix_isSymmetricFiniteMatrix
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (r : Fin m → ℝ) (y : Fin n → ℝ) :
    IsSymmetricFiniteMatrix (lsNormwiseBackwardErrorEigenMatrix theta A r y) := by
  intro i k
  exact lsNormwiseBackwardErrorEigenMatrix_apply_comm theta A r y i k
/-- `lambda_* I <= A A^T - mu rr^T / ||y||_2^2` in finite Loewner order. -/
theorem lsNormwiseBackwardErrorLambdaStar_smul_id_finiteLoewnerLe_eigenMatrix
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ) :
    finiteLoewnerLe
      (fun i k : Fin (m + 1) =>
        lsNormwiseBackwardErrorLambdaStar theta A r y * finiteIdMatrix i k)
      (lsNormwiseBackwardErrorEigenMatrix theta A r y) := by
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    lsNormwiseBackwardErrorEigenMatrix theta A r y
  let hM : IsSymmetricFiniteMatrix M :=
    lsNormwiseBackwardErrorEigenMatrix_isSymmetricFiniteMatrix theta A r y
  apply finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues M hM
  intro a
  unfold finiteHermitianEigenvalues
  rw [Matrix.IsHermitian.eigenvalues]
  exact
    lsNormwiseBackwardErrorLambdaStar_le_eigenvalues₀ theta A r y
      ((Fintype.equivOfCardEq
        (Fintype.card_fin (Fintype.card (Fin (m + 1))))).symm a)
/-- Rayleigh lower bound from the least Hermitian eigenvalue `lambda_*`. -/
theorem lsNormwiseBackwardErrorLambdaStar_mul_vecNorm2Sq_le_eigenMatrix_quadraticForm
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (r : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (p : Fin (m + 1) → ℝ) :
    lsNormwiseBackwardErrorLambdaStar theta A r y * vecNorm2Sq p ≤
      finiteQuadraticForm (lsNormwiseBackwardErrorEigenMatrix theta A r y) p := by
  have hle :=
    lsNormwiseBackwardErrorLambdaStar_smul_id_finiteLoewnerLe_eigenMatrix
      theta A r y p
  rw [finiteQuadraticForm_smul_finiteIdMatrix] at hle
  simpa [finiteVecNorm2Sq, vecNorm2Sq] using hle
/-- If the source residual is zero, the Theorem 20.5 eigenmatrix is the
    positive-semidefinite row Gram `A A^T`.  Hence `lambda_*` is nonnegative
    and the printed eigenvalue formula selects its zero `phi` branch. -/
theorem lsNormwiseBackwardErrorEigenvalueFormulaRHS_eq_zero_of_residual_eq_zero
    {m n : ℕ} (theta : ℝ) (A : Fin (m + 1) → Fin n → ℝ)
    (b : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (hres : lsResidualHigham A b y = 0) :
    lsNormwiseBackwardErrorEigenvalueFormulaRHS theta A b y = 0 := by
  let r : Fin (m + 1) → ℝ := lsResidualHigham A b y
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    lsNormwiseBackwardErrorEigenMatrix theta A r y
  let hM : IsSymmetricFiniteMatrix M :=
    lsNormwiseBackwardErrorEigenMatrix_isSymmetricFiniteMatrix theta A r y
  have hr : r = 0 := by simpa [r] using hres
  have hMgram :
      M = fun i k : Fin (m + 1) => ∑ j : Fin n, A i j * A k j := by
    ext i k
    simp [M, lsNormwiseBackwardErrorEigenMatrix, hr]
  have hPSD : finitePSD M := by
    intro p
    rw [hMgram,
      finiteQuadraticForm_rowGram_transpose_eq_vecNorm2Sq_rectMatMulVec_finiteTranspose]
    exact vecNorm2Sq_nonneg _
  have heigs : ∀ i : Fin (m + 1),
      0 ≤ finiteHermitianEigenvalues M hM i :=
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg M hM).mp hPSD
  let e : Fin (Fintype.card (Fin (m + 1))) ≃ Fin (m + 1) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let a0 : Fin (Fintype.card (Fin (m + 1))) :=
    lsNormwiseBackwardErrorLambdaStarIndex m
  let a : Fin (m + 1) := e a0
  have hlambda_eq :
      finiteHermitianEigenvalues M hM a =
        lsNormwiseBackwardErrorLambdaStar theta A r y := by
    unfold finiteHermitianEigenvalues lsNormwiseBackwardErrorLambdaStar
    simp only [Matrix.IsHermitian.eigenvalues]
    congr 1
    simp [e, a0, a]
  have hlambda :
      0 ≤ lsNormwiseBackwardErrorLambdaStar theta A r y := by
    rw [← hlambda_eq]
    exact heigs a
  unfold lsNormwiseBackwardErrorEigenvalueFormulaRHS
  rw [show lsResidualHigham A b y = r from rfl]
  rw [lsNormwiseBackwardErrorEigenvalueFormulaValue_eq_phi_of_lambdaStar_nonneg
    theta A r y hlambda]
  exact lsNormwiseBackwardErrorPhi_eq_zero_of_residual_eq_zero theta y hr
/-- Higham, 2nd ed., Chapter 20, equations (20.20)-(20.21):
    feasibility for the normwise backward-error problem is equivalent to the
    perturbed rectangular normal equations for the same candidate `y`.  This is
    the local least-squares-consistency characterization used by the WKS route. -/
theorem LSNormwiseBackwardErrorFeasible.iff_rectLSNormalEquations {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ↔
      RectLSNormalEquations
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y := by
  simpa [LSNormwiseBackwardErrorFeasible] using
    (RectLSNormalEquations.iff_isLeastSquaresMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) y).symm
/-- Residual-orthogonality form of
    `LSNormwiseBackwardErrorFeasible.iff_rectLSNormalEquations`. -/
theorem LSNormwiseBackwardErrorFeasible.iff_perturbed_residual_orthogonal
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab ↔
      ∀ j : Fin n,
        ∑ i : Fin m, (A i j + DeltaA i j) *
          lsResidual
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i) y i = 0 := by
  exact
    (LSNormwiseBackwardErrorFeasible.iff_rectLSNormalEquations
      A b y DeltaA Deltab).trans
      (RectLSNormalEquations.iff_residual_orthogonal
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y)
/-- Extra outer-product perturbation used by the rank-two WKS construction.
    It has left vector `q` and right vector `y`, scaled so that its action on
    `y` is `beta q`. -/
noncomputable def lsNormwiseBackwardErrorRankTwoExtraDeltaA {m n : ℕ}
    (beta : ℝ) (q : Fin m → ℝ) (y : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => (beta / vecNorm2Sq y) * q i * y j
/-- The extra rank-two outer-product perturbation sends `y` to `beta q`. -/
theorem lsNormwiseBackwardErrorRankTwoExtraDeltaA_mulVec
    {m n : ℕ} {beta : ℝ} (q : Fin m → ℝ)
    {y : Fin n → ℝ} (hy : vecNorm2Sq y ≠ 0) :
    rectMatMulVec (lsNormwiseBackwardErrorRankTwoExtraDeltaA beta q y) y =
      fun i : Fin m => beta * q i := by
  ext i
  unfold rectMatMulVec lsNormwiseBackwardErrorRankTwoExtraDeltaA
  calc
    ∑ j : Fin n, (beta / vecNorm2Sq y * q i * y j) * y j
        = (beta / vecNorm2Sq y * q i) * ∑ j : Fin n, y j ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = beta * q i := by
            change (beta / vecNorm2Sq y * q i) * vecNorm2Sq y = beta * q i
            field_simp [hy]
/-- If the extra rank-two left vector is orthogonal to `p`, the extra
    perturbation does not change the source-transpose action on `p`. -/
theorem lsNormwiseBackwardErrorRankTwoExtraDeltaA_transpose_mul_eq_zero
    {m n : ℕ} (beta : ℝ) (q p : Fin m → ℝ) (y : Fin n → ℝ)
    (hq_orth : ∑ i : Fin m, q i * p i = 0) :
    (fun j : Fin n =>
      ∑ i : Fin m,
        lsNormwiseBackwardErrorRankTwoExtraDeltaA beta q y i j * p i) =
      0 := by
  ext j
  unfold lsNormwiseBackwardErrorRankTwoExtraDeltaA
  calc
    ∑ i : Fin m, (beta / vecNorm2Sq y * q i * y j) * p i
        = (beta / vecNorm2Sq y * y j) * ∑ i : Fin m, q i * p i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := by rw [hq_orth, mul_zero]
/-- Source-shaped numerator for the optimal scalar in the scaled rank-one WKS
    witness.  When `r = b - A*y` and `u = A^T p`, the scalar numerator
    `p^T r + u^T y` is exactly `p^T b`. -/
theorem lsNormwiseBackwardErrorRankOne_scaled_optimal_scale_num_eq_dot_b
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (p : Fin m → ℝ) :
    let r : Fin m → ℝ := lsResidualHigham A b y
    let u : Fin n → ℝ := fun j => ∑ i : Fin m, A i j * p i
    (∑ k : Fin m, p k * r k) + (∑ j : Fin n, u j * y j) =
      ∑ i : Fin m, p i * b i := by
  let r : Fin m → ℝ := lsResidualHigham A b y
  let u : Fin n → ℝ := fun j => ∑ i : Fin m, A i j * p i
  have hres :
      (∑ k : Fin m, p k * r k) =
        (∑ k : Fin m, p k * b k) -
          ∑ k : Fin m, ∑ j : Fin n, p k * (A k j * y j) := by
    calc
      (∑ k : Fin m, p k * r k)
          = ∑ k : Fin m, p k * (b k - ∑ j : Fin n, A k j * y j) := by
              rfl
      _ = ∑ k : Fin m,
            (p k * b k - p k * (∑ j : Fin n, A k j * y j)) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ =
          (∑ k : Fin m, p k * b k) -
            ∑ k : Fin m, p k * (∑ j : Fin n, A k j * y j) := by
          rw [Finset.sum_sub_distrib]
      _ =
          (∑ k : Fin m, p k * b k) -
            ∑ k : Fin m, ∑ j : Fin n, p k * (A k j * y j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
  have hu :
      (∑ j : Fin n, u j * y j) =
        ∑ k : Fin m, ∑ j : Fin n, p k * (A k j * y j) := by
    calc
      (∑ j : Fin n, u j * y j)
          = ∑ j : Fin n, (∑ k : Fin m, A k j * p k) * y j := by
              rfl
      _ = ∑ j : Fin n, ∑ k : Fin m, (A k j * p k) * y j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
      _ = ∑ k : Fin m, ∑ j : Fin n, (A k j * p k) * y j := by
              rw [Finset.sum_comm]
      _ = ∑ k : Fin m, ∑ j : Fin n, p k * (A k j * y j) := by
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro j _
              ring
  change
    (∑ k : Fin m, p k * r k) + (∑ j : Fin n, u j * y j) =
      ∑ i : Fin m, p i * b i
  rw [hres, hu]
  ring
/-- Divided source-shaped form of the optimal scalar in the scaled rank-one WKS
    witness.  Under the source residual convention, the optimal scale is
    `(p^T b) / ||p||_2^2`. -/
theorem lsNormwiseBackwardErrorRankOne_scaled_optimal_scale_eq_dot_b_div
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (p : Fin m → ℝ) :
    let r : Fin m → ℝ := lsResidualHigham A b y
    let u : Fin n → ℝ := fun j => ∑ i : Fin m, A i j * p i
    (((∑ k : Fin m, p k * r k) + (∑ j : Fin n, u j * y j)) /
        vecNorm2Sq p) =
      (∑ i : Fin m, p i * b i) / vecNorm2Sq p := by
  let r : Fin m → ℝ := lsResidualHigham A b y
  let u : Fin n → ℝ := fun j => ∑ i : Fin m, A i j * p i
  have hnum :
      (∑ k : Fin m, p k * r k) + (∑ j : Fin n, u j * y j) =
        ∑ i : Fin m, p i * b i := by
    simpa [r, u] using
      lsNormwiseBackwardErrorRankOne_scaled_optimal_scale_num_eq_dot_b A b y p
  change
    (((∑ k : Fin m, p k * r k) + (∑ j : Fin n, u j * y j)) /
        vecNorm2Sq p) =
      (∑ i : Fin m, p i * b i) / vecNorm2Sq p
  rw [hnum]
/-- Division-free squared-cost bridge for the scaled rank-one WKS witness.
    A future singular-vector construction naturally supplies the scaled witness
    cost as a squared inequality after multiplying by `||p||_2^2`; this lemma
    converts that certificate into the square-root form used by the
    source-block `sigma_min` handoff. -/
theorem lsNormwiseBackwardErrorRankOne_scaled_cost_sqrt_le_of_sq_le
    {m n : ℕ} (theta sigma : ℝ)
    (p : Fin m → ℝ) (hp : vecNorm2Sq p ≠ 0)
    (u : Fin n → ℝ) (q : Fin m → ℝ)
    (hsigma : 0 ≤ sigma)
    (hcost_sq :
      vecNorm2Sq u + theta ^ 2 * vecNorm2Sq q * vecNorm2Sq p ≤
        sigma ^ 2 * vecNorm2Sq p) :
    Real.sqrt (vecNorm2Sq u / vecNorm2Sq p +
      theta ^ 2 * vecNorm2Sq q) ≤ sigma := by
  have hp_pos : 0 < vecNorm2Sq p :=
    lt_of_le_of_ne (vecNorm2Sq_nonneg p) (Ne.symm hp)
  have hinside_le :
      vecNorm2Sq u / vecNorm2Sq p + theta ^ 2 * vecNorm2Sq q ≤
        sigma ^ 2 := by
    have hmul :
        (vecNorm2Sq u / vecNorm2Sq p + theta ^ 2 * vecNorm2Sq q) *
            vecNorm2Sq p ≤
          sigma ^ 2 * vecNorm2Sq p := by
      calc
        (vecNorm2Sq u / vecNorm2Sq p + theta ^ 2 * vecNorm2Sq q) *
            vecNorm2Sq p
            = vecNorm2Sq u + theta ^ 2 * vecNorm2Sq q * vecNorm2Sq p := by
                field_simp [ne_of_gt hp_pos]
        _ ≤ sigma ^ 2 * vecNorm2Sq p := hcost_sq
    exact le_of_mul_le_mul_right hmul hp_pos
  calc
    Real.sqrt (vecNorm2Sq u / vecNorm2Sq p +
        theta ^ 2 * vecNorm2Sq q)
        ≤ Real.sqrt (sigma ^ 2) := Real.sqrt_le_sqrt hinside_le
    _ = sigma := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsigma]
/-- Frobenius upper bound for the left perturbation block in the WKS
    source-block transpose action. -/
theorem LSNormwiseBackwardErrorFeasible.formulaMatrix_transpose_source_residual_left_vecNorm2_le
    {m n : ℕ} (A : Fin (m + 1) → Fin n → ℝ)
    (b : Fin (m + 1) → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin (m + 1) → Fin n → ℝ)
    (Deltab : Fin (m + 1) → ℝ) :
    vecNorm2
        (fun j : Fin n =>
          -∑ i : Fin (m + 1), DeltaA i j *
            (lsResidualHigham A b y i + Deltab i -
              rectMatMulVec DeltaA y i)) ≤
      frobNormRect DeltaA *
        vecNorm2
          (fun i : Fin (m + 1) =>
            lsResidualHigham A b y i + Deltab i -
              rectMatMulVec DeltaA y i) := by
  let p : Fin (m + 1) → ℝ :=
    fun i => lsResidualHigham A b y i + Deltab i - rectMatMulVec DeltaA y i
  have hbound :=
    vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul DeltaA p
  have hleft :
      (fun j : Fin n => -∑ i : Fin (m + 1), DeltaA i j * p i) =
        fun j : Fin n => -rectMatMulVec (finiteTranspose DeltaA) p j := by
    ext j
    simp [rectMatMulVec, finiteTranspose]
  change
    vecNorm2 (fun j : Fin n => -∑ i : Fin (m + 1), DeltaA i j * p i) ≤
      frobNormRect DeltaA * vecNorm2 p
  rw [hleft, vecNorm2_neg]
  exact hbound

end NumStability
