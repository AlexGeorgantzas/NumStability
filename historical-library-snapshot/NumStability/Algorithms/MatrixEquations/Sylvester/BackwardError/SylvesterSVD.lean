import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.Specification
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.BackwardError.SylvesterSVD

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

/-- **SVD representation**: Y = U · diag(σ) · Vᵀ.
    We represent this as the pointwise identity
    Y_{ij} = ∑_k U_{ik} σ_k V_{jk}. -/
def IsSVD (n : ℕ) (Y : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) : Prop :=
  IsOrthogonal n U ∧ IsOrthogonal n V ∧
  (∀ i j, Y i j = ∑ k : Fin n, U i k * (σ k * V j k)) ∧
  (∀ i, 0 ≤ σ i)

-- ============================================================
-- Transformed residual in SVD coordinates (§16.2, eq 16.13)
-- ============================================================

/-- **Transformed residual** in SVD coordinates: R̃ = UᵀRV where
    R is the Sylvester residual. -/
noncomputable def svdResidual (n : ℕ)
    (U V : Fin n → Fin n → ℝ)
    (R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (matTranspose U) R) V

/-- The SVD-transformed residual has the same Frobenius norm as R:
    ‖R̃‖²_F = ‖R‖²_F, since orthogonal transformations preserve ‖·‖_F. -/
theorem svdResidual_frobNormSq (n : ℕ) (U V R : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    frobNormSq (svdResidual n U V R) = frobNormSq R := by
  unfold svdResidual
  -- ‖(UᵀR)V‖²_F = ‖UᵀR‖²_F = ‖R‖²_F
  rw [frobNormSq_orthogonal_right _ _ hV, frobNormSq_orthogonal_left _ _ hU.transpose]

-- ============================================================
-- Backward error ξ² definition (§16.2, eq 16.16)
-- ============================================================

/-- **ξ² functional** (eq 16.16): given transformed residual R̃ and
    singular values σ, with tolerances α, β, γ:
      ξ² = ∑_{i,j} r̃²_{ij} / (α²σ²_j + β²σ²_i + γ²). -/
noncomputable def xiSq (n : ℕ) (R_tilde : Fin n → Fin n → ℝ)
    (σ : Fin n → ℝ) (α β γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    R_tilde i j ^ 2 / (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)

/-- ξ² is nonneg when all denominators are positive. -/
lemma xiSq_nonneg {n : ℕ} (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    0 ≤ xiSq n R_tilde σ α β γ := by
  unfold xiSq
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hpos i j))
























-- ============================================================
-- Backward error lower bound (§16.2, eq 16.15 lower)
-- ============================================================

/-- **Backward error lower bound** (eq 16.15, lower direction):
    For ANY perturbations ΔÃ, ΔB̃, ΔC̃ satisfying the entry-wise
    backward error equation ΔÃ_{ij}σ_j - σ_iΔB̃_{ij} - ΔC̃_{ij} = R̃_{ij},
    we have ξ² ≤ ‖ΔÃ‖²_F/α² + ‖ΔB̃‖²_F/β² + ‖ΔC̃‖²_F/γ².

    This is a consequence of the Cauchy-Schwarz inequality applied entry by
    entry: R̃² = (ασ_j · ΔÃ/α - βσ_i · ΔB̃/β - γ · ΔC̃/γ)²
    ≤ (α²σ²_j + β²σ²_i + γ²)(ΔÃ²/α² + ΔB̃²/β² + ΔC̃²/γ²). -/
theorem backward_error_lower_sq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (DA DB DC : Fin n → Fin n → ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * σ j - σ i * DB i j - DC i j = R_tilde i j) :
    xiSq n R_tilde σ α β γ ≤
    ∑ i : Fin n, ∑ j : Fin n,
      (DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2) := by
  unfold xiSq
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  have hd := hpos i j
  -- R̃² / denom ≤ ΔA²/α² + ΔB²/β² + ΔC²/γ²
  rw [div_le_iff₀ hd, ← hEq i j]
  -- (ΔA·σ_j - σ_i·ΔB - ΔC)² ≤ (ΔA²/α² + ΔB²/β² + ΔC²/γ²)(α²σ²_j + β²σ²_i + γ²)
  -- Goal: (DA·σ_j - σ_i·DB - DC)² ≤ (DA²/α² + DB²/β² + DC²/γ²) · denom
  -- Suffices to prove: denom · LHS ≤ denom · RHS, i.e.,
  -- (DA·σ_j - σ_i·DB - DC)² · 1 ≤ (DA²/α² + DB²/β² + DC²/γ²) · denom
  -- By Cauchy-Schwarz: (ασ_j·(DA/α) + (-βσ_i)·(DB/β) + (-γ)·(DC/γ))²
  --   ≤ (α²σ²_j + β²σ²_i + γ²) · (DA²/α² + DB²/β² + DC²/γ²)
  -- We verify: ασ_j·(DA/α) = DA·σ_j, βσ_i·(DB/β) = σ_i·DB, γ·(DC/γ) = DC ✓
  -- Multiply both sides by α²β²γ² to clear denominators:
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  rw [show DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2 =
      (DA i j ^ 2 * β ^ 2 * γ ^ 2 + DB i j ^ 2 * α ^ 2 * γ ^ 2 +
       DC i j ^ 2 * α ^ 2 * β ^ 2) / (α ^ 2 * β ^ 2 * γ ^ 2) from by
    field_simp]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity)]
  -- Cauchy-Schwarz: (∑ a_k x_k)² ≤ (∑ a²_k)(∑ x²_k)
  -- a = (ασ_j, -βσ_i, -γ), x = (DA·βγ, DB·αγ, DC·αβ)
  -- (∑ ax)² = (αβγ(DA·σ_j - σ_i·DB - DC))²
  -- Hints: three cross-term squares that encode Cauchy-Schwarz
  nlinarith [sq_nonneg (α * σ j * DB i j * α * γ - (-β * σ i) * DA i j * β * γ),
             sq_nonneg (α * σ j * DC i j * α * β - (-γ) * DA i j * β * γ),
             sq_nonneg ((-β * σ i) * DC i j * α * β - (-γ) * DB i j * α * γ)]






-- ============================================================
-- Backward error upper bound (§16.2, eq 16.15 upper)
-- ============================================================

/-- **Backward error upper bound** (eq 16.15, upper direction):
    The optimal perturbations in SVD coordinates achieve cost exactly ξ².
    We prove one component: ∑ (Δã_opt)² ≤ α² · ξ² where
      Δã_opt_{ij} = α²σ_j · r̃_{ij} / (α²σ²_j + β²σ²_i + γ²). -/
theorem backward_error_upper_component (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    ∑ i : Fin n, ∑ j : Fin n,
      (α ^ 2 * σ j * R_tilde i j /
       (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2 ≤
    α ^ 2 * xiSq n R_tilde σ α β γ := by
  unfold xiSq; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  have hd := hpos i j
  have hd_ne : (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ≠ 0 := ne_of_gt hd
  -- (α²σ_j r̃ / d)² ≤ α² · (r̃² / d)
  -- Multiply out: α⁴σ²_j r̃² ≤ α² r̃² d = α² r̃²(α²σ²_j + β²σ²_i + γ²)
  -- which simplifies to α²σ²_j ≤ α²σ²_j + β²σ²_i + γ² ✓
  -- (α²σ_j r̃ / d)² = α⁴σ²_j r̃² / d²
  -- α²(r̃²/d) = α² r̃² / d
  -- Need: α⁴σ²_j r̃²/d² ≤ α² r̃²/d, i.e., α⁴σ²_j r̃² · d ≤ α² r̃² · d²
  -- i.e., α²σ²_j ≤ d = α²σ²_j + β²σ²_i + γ² ✓
  have key : (α ^ 2 * σ j * R_tilde i j) ^ 2 ≤
      α ^ 2 * R_tilde i j ^ 2 *
      (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
    nlinarith [sq_nonneg (R_tilde i j * β * σ i), sq_nonneg (R_tilde i j * γ)]
  calc (α ^ 2 * σ j * R_tilde i j /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2
      = (α ^ 2 * σ j * R_tilde i j) ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        rw [div_pow]
    _ ≤ (α ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right key (sq_nonneg _)
    _ = α ^ 2 * R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
        rw [sq]; field_simp
    _ = α ^ 2 * (R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) := by
        rw [mul_div_assoc]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    optimal SVD-coordinate perturbation in the `DeltaA` slot. -/
noncomputable def svdOptimalDeltaA (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    α ^ 2 * σ j * R_tilde i j /
      (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    optimal SVD-coordinate perturbation in the `DeltaB` slot. -/
noncomputable def svdOptimalDeltaB (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    -(β ^ 2 * σ i * R_tilde i j) /
      (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    optimal SVD-coordinate perturbation in the `DeltaC` slot. -/
noncomputable def svdOptimalDeltaC (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    -(γ ^ 2 * R_tilde i j) /
      (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)

/-- The coordinatewise optimal perturbations solve the uncoupled residual
    equation used in (16.14)-(16.15). -/
theorem svdOptimalPerturbations_scalar_eq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    ∀ i j : Fin n,
      svdOptimalDeltaA n R_tilde σ α β γ i j * σ j -
          σ i * svdOptimalDeltaB n R_tilde σ α β γ i j -
            svdOptimalDeltaC n R_tilde σ α β γ i j =
        R_tilde i j := by
  intro i j
  unfold svdOptimalDeltaA svdOptimalDeltaB svdOptimalDeltaC
  have hd_ne :
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 ≠ 0 :=
    ne_of_gt (hpos i j)
  field_simp [hd_ne]
  ring

/-- The coordinatewise optimal perturbations attain total normalized squared
    cost exactly `xiSq`.  This is the constructive upper-side dependency for
    Higham's equation (16.15). -/
theorem svdOptimalPerturbations_cost_eq_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    ∑ i : Fin n, ∑ j : Fin n,
      (svdOptimalDeltaA n R_tilde σ α β γ i j ^ 2 / α ^ 2 +
        svdOptimalDeltaB n R_tilde σ α β γ i j ^ 2 / β ^ 2 +
          svdOptimalDeltaC n R_tilde σ α β γ i j ^ 2 / γ ^ 2) =
      xiSq n R_tilde σ α β γ := by
  unfold xiSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold svdOptimalDeltaA svdOptimalDeltaB svdOptimalDeltaC
  have hd_ne :
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 ≠ 0 :=
    ne_of_gt (hpos i j)
  field_simp [hd_ne]

/-- Existence form of the optimal SVD-coordinate perturbations: they solve the
    uncoupled equation and have total normalized squared cost `xiSq`. -/
theorem exists_svdOptimalPerturbations (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    ∃ DA DB DC : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, DA i j * σ j - σ i * DB i j - DC i j = R_tilde i j) ∧
        (∑ i : Fin n, ∑ j : Fin n,
          (DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2)) =
          xiSq n R_tilde σ α β γ := by
  refine ⟨svdOptimalDeltaA n R_tilde σ α β γ,
    svdOptimalDeltaB n R_tilde σ α β γ,
    svdOptimalDeltaC n R_tilde σ α β γ, ?_, ?_⟩
  · exact svdOptimalPerturbations_scalar_eq n R_tilde σ α β γ hpos
  · exact svdOptimalPerturbations_cost_eq_xiSq n R_tilde σ α β γ hpos

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper direction:
    the `DeltaA` component of the coordinatewise optimizer has squared
    Frobenius norm bounded by `alpha^2 * xiSq`. -/
theorem svdOptimalDeltaA_frobNormSq_le_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    frobNormSq (svdOptimalDeltaA n R_tilde σ α β γ) ≤
      α ^ 2 * xiSq n R_tilde σ α β γ := by
  simpa [frobNormSq, svdOptimalDeltaA] using
    backward_error_upper_component n R_tilde σ α β γ hpos

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper direction:
    the `DeltaB` component of the coordinatewise optimizer has squared
    Frobenius norm bounded by `beta^2 * xiSq`. -/
theorem svdOptimalDeltaB_frobNormSq_le_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    frobNormSq (svdOptimalDeltaB n R_tilde σ α β γ) ≤
      β ^ 2 * xiSq n R_tilde σ α β γ := by
  unfold frobNormSq xiSq svdOptimalDeltaB
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hd_ne :
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 ≠ 0 :=
    ne_of_gt (hpos i j)
  have key : (β ^ 2 * σ i * R_tilde i j) ^ 2 ≤
      β ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
    nlinarith [sq_nonneg (R_tilde i j * α * σ j), sq_nonneg (R_tilde i j * γ)]
  calc
    (-(β ^ 2 * σ i * R_tilde i j) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2
        = (β ^ 2 * σ i * R_tilde i j /
            (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2 := by
            ring
    _ = (β ^ 2 * σ i * R_tilde i j) ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        rw [div_pow]
    _ ≤ (β ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right key (sq_nonneg _)
    _ = β ^ 2 * R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
        rw [sq]
        field_simp [hd_ne]
    _ = β ^ 2 * (R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) := by
        rw [mul_div_assoc]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper direction:
    the `DeltaC` component of the coordinatewise optimizer has squared
    Frobenius norm bounded by `gamma^2 * xiSq`. -/
theorem svdOptimalDeltaC_frobNormSq_le_xiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    frobNormSq (svdOptimalDeltaC n R_tilde σ α β γ) ≤
      γ ^ 2 * xiSq n R_tilde σ α β γ := by
  unfold frobNormSq xiSq svdOptimalDeltaC
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hd_ne :
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 ≠ 0 :=
    ne_of_gt (hpos i j)
  have key : (γ ^ 2 * R_tilde i j) ^ 2 ≤
      γ ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
    nlinarith [sq_nonneg (R_tilde i j * α * σ j), sq_nonneg (R_tilde i j * β * σ i)]
  calc
    (-(γ ^ 2 * R_tilde i j) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2
        = (γ ^ 2 * R_tilde i j /
            (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2 := by
            ring
    _ = (γ ^ 2 * R_tilde i j) ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        rw [div_pow]
    _ ≤ (γ ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right key (sq_nonneg _)
    _ = γ ^ 2 * R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
        rw [sq]
        field_simp [hd_ne]
    _ = γ ^ 2 * (R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) := by
        rw [mul_div_assoc]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper direction:
    all three coordinatewise optimizer components satisfy the squared
    Frobenius bounds needed for the later backward-error certificate. -/
theorem svdOptimalPerturbations_frobNormSq_bounds (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    frobNormSq (svdOptimalDeltaA n R_tilde σ α β γ) ≤
        α ^ 2 * xiSq n R_tilde σ α β γ ∧
      frobNormSq (svdOptimalDeltaB n R_tilde σ α β γ) ≤
        β ^ 2 * xiSq n R_tilde σ α β γ ∧
      frobNormSq (svdOptimalDeltaC n R_tilde σ α β γ) ≤
        γ ^ 2 * xiSq n R_tilde σ α β γ := by
  exact ⟨svdOptimalDeltaA_frobNormSq_le_xiSq n R_tilde σ α β γ hpos,
    svdOptimalDeltaB_frobNormSq_le_xiSq n R_tilde σ α β γ hpos,
    svdOptimalDeltaC_frobNormSq_le_xiSq n R_tilde σ α β γ hpos⟩


































-- ============================================================
-- Amplification factor (§16.2, eqs 16.17-16.19)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.18):
    scalar amplification factor `mu` comparing the backward error scale with
    the normwise relative residual.  The singular-value arguments are the
    source's zero-extended `sigma_m` and `sigma_n` slots for an `m x n`
    approximate solution. -/
noncomputable def sylvesterAmplificationMu
    (α β γ yNorm σm σn : ℝ) : ℝ :=
  ((α + β) * yNorm + γ) /
    Real.sqrt (α ^ 2 * σn ^ 2 + β ^ 2 * σm ^ 2 + γ ^ 2)






/-- Higham, 2nd ed., Chapter 16.2, equation (16.19):
    square-case specialization of the amplification factor. -/
noncomputable def sylvesterAmplificationMuSquare
    (α β γ yNorm σmin : ℝ) : ℝ :=
  ((α + β) * yNorm + γ) /
    Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2)






/-- In the square case, the two singular-value slots in (16.18) coincide,
    giving the source formula (16.19). -/
theorem sylvesterAmplificationMu_square_eq
    (α β γ yNorm σmin : ℝ) :
    sylvesterAmplificationMu α β γ yNorm σmin σmin =
      sylvesterAmplificationMuSquare α β γ yNorm σmin := by
  unfold sylvesterAmplificationMu sylvesterAmplificationMuSquare
  rw [show α ^ 2 * σmin ^ 2 + β ^ 2 * σmin ^ 2 + γ ^ 2 =
      (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2 by ring]






/-- Higham, 2nd ed., Chapter 16.2, prose after equation (16.18):
    in the square case the amplification factor is at least one, provided the
    singular-value slot is bounded by the Frobenius norm of the approximate
    solution.  The latter is the singular-value foundation still kept explicit
    in this square API. -/
theorem one_le_sylvesterAmplificationMuSquare
    (α β γ yNorm σmin : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hy : 0 ≤ yNorm) (hσ : 0 ≤ σmin) (hσ_le : σmin ≤ yNorm)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) :
    1 ≤ sylvesterAmplificationMuSquare α β γ yNorm σmin := by
  unfold sylvesterAmplificationMuSquare
  have hsqrt_pos :
      0 < Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) :=
    Real.sqrt_pos.2 hDenom
  have hσsq : σmin ^ 2 ≤ yNorm ^ 2 :=
    (sq_le_sq₀ hσ hy).mpr hσ_le
  have hN_nonneg : 0 ≤ (α + β) * yNorm + γ := by
    nlinarith [mul_nonneg (add_nonneg hα hβ) hy]
  have hD_le :
      (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2 ≤
        ((α + β) * yNorm + γ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hσsq (sq_nonneg α),
      mul_le_mul_of_nonneg_left hσsq (sq_nonneg β),
      mul_nonneg hα hβ,
      mul_nonneg (add_nonneg hα hβ) hy,
      mul_nonneg hγ (mul_nonneg (add_nonneg hα hβ) hy)]
  have hsqrt_le :
      Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) ≤
        (α + β) * yNorm + γ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hN_nonneg).mp
    rw [Real.sq_sqrt (le_of_lt hDenom)]
    exact hD_le
  exact (one_le_div hsqrt_pos).mpr hsqrt_le






/-- **Amplification factor bound** (eqs 16.17-16.18):
    ξ² ≤ ‖R̃‖²_F / ((α²+β²)σ²_min + γ²)
    when all singular values satisfy σ_i ≥ σ_min.

    Combined with ‖R̃‖²_F = ‖R‖²_F (orthogonal invariance), this gives
    ξ ≤ ‖R‖_F / √((α²+β²)σ²_min + γ²). -/
theorem xiSq_amplification_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ) (hσ_min : ∀ i : Fin n, σ_min ≤ σ i)
    (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) :
    xiSq n R_tilde σ α β γ ≤
    frobNormSq R_tilde / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
  unfold xiSq
  -- Each term: r̃²/(α²σ²_j + β²σ²_i + γ²) ≤ r̃²/((α²+β²)σ²_min + γ²)
  -- Sum of RHS = (∑∑ r̃²) / d = ‖R̃‖²_F / d
  have hd_ne : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  -- First show ∑∑ r̃²/denom_ij ≤ ∑∑ r̃²/denom_min
  suffices h : ∑ i : Fin n, ∑ j : Fin n,
      R_tilde i j ^ 2 / (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n,
      R_tilde i j ^ 2 / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) by
    rwa [show ∑ i : Fin n, ∑ j : Fin n,
        R_tilde i j ^ 2 / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) =
        frobNormSq R_tilde / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) from by
      unfold frobNormSq
      rw [eq_div_iff hd_ne]
      rw [Finset.sum_mul]; congr 1; ext i
      rw [Finset.sum_mul]; congr 1; ext j
      exact div_mul_cancel₀ _ hd_ne] at h
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  have hσi : σ_min ^ 2 ≤ σ i ^ 2 :=
    sq_le_sq' (by linarith [hσ_min i]) (hσ_min i)
  have hσj : σ_min ^ 2 ≤ σ j ^ 2 :=
    sq_le_sq' (by linarith [hσ_min j]) (hσ_min j)
  have hdenom_le : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≤
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 := by nlinarith [sq_nonneg α, sq_nonneg β]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hDenom hdenom_le

/-- **Amplification factor with orthogonal invariance** (eq 16.19, m=n case):
    ξ² ≤ ‖R‖²_F / ((α²+β²)σ²_min + γ²). -/
theorem amplification_factor_bound (n : ℕ)
    (Y R : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hσ_min : ∀ i : Fin n, σ_min ≤ σ i) (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) :
    xiSq n (svdResidual n U V R) σ α β γ ≤
    frobNormSq R / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
  have hle := xiSq_amplification_bound n (svdResidual n U V R) σ α β γ σ_min
    hσ_min hσ_min_nn hDenom
  rw [svdResidual_frobNormSq n U V R hSVD.1 hSVD.2.1] at hle
  exact hle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.17)-(16.19):
    the existing square xi-squared residual bound written with the source's
    amplification factor `mu`.  This is still a bound for `xi`; the separate
    optimizer step relating `eta(Y)` and `xi` remains the open part of
    equation (16.15). -/
theorem xiSq_le_mu_relative_residual_sq (n : ℕ)
    (Y R : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hσ_min : ∀ i : Fin n, σ_min ≤ σ i) (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2)
    (hScale : 0 < (α + β) * frobNorm Y + γ) :
    xiSq n (svdResidual n U V R) σ α β γ ≤
      (sylvesterAmplificationMuSquare α β γ (frobNorm Y) σ_min *
        (frobNorm R / ((α + β) * frobNorm Y + γ))) ^ 2 := by
  have hle := amplification_factor_bound n Y R U V σ α β γ σ_min
    hSVD hσ_min hσ_min_nn hDenom
  have hScale_ne : (α + β) * frobNorm Y + γ ≠ 0 := ne_of_gt hScale
  have hD_ne : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  have hSqrt_ne : Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hDenom)
  have hSqrt_sq :
      Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) ^ 2 =
        (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 :=
    Real.sq_sqrt (le_of_lt hDenom)
  calc
    xiSq n (svdResidual n U V R) σ α β γ ≤
        frobNormSq R / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := hle
    _ = (sylvesterAmplificationMuSquare α β γ (frobNorm Y) σ_min *
        (frobNorm R / ((α + β) * frobNorm Y + γ))) ^ 2 := by
        unfold sylvesterAmplificationMuSquare
        have hmul :
            ((α + β) * frobNorm Y + γ) /
                Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) *
              (frobNorm R / ((α + β) * frobNorm Y + γ)) =
                frobNorm R /
                  Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
          field_simp [hScale_ne, hSqrt_ne]
        rw [hmul, div_pow, hSqrt_sq, frobNorm_sq]



















-- ============================================================
-- Backward error η bound via cost (§16.2)
-- ============================================================

/-- **Backward error η bound via perturbation cost**:
    If ‖ΔA‖²_F ≤ η²α², ‖ΔB‖²_F ≤ η²β², ‖ΔC‖²_F ≤ η²γ²,
    and the entry-wise backward error equation holds in SVD coordinates,
    then ξ² ≤ η²(α² + β² + γ²). -/
theorem backward_error_eta_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (DA DB DC : Fin n → Fin n → ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * σ j - σ i * DB i j - DC i j = R_tilde i j)
    (hDA : frobNormSq DA ≤ (η * α) ^ 2)
    (hDB : frobNormSq DB ≤ (η * β) ^ 2)
    (hDC : frobNormSq DC ≤ (η * γ) ^ 2) :
    xiSq n R_tilde σ α β γ ≤ 3 * η ^ 2 := by
  have hle := backward_error_lower_sq n R_tilde σ α β γ hα hβ hγ DA DB DC hpos hEq
  -- ξ² ≤ ∑ (DA²/α² + DB²/β² + DC²/γ²) = ‖DA‖²_F/α² + ‖DB‖²_F/β² + ‖DC‖²_F/γ²
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2) =
      frobNormSq DA / α ^ 2 + frobNormSq DB / β ^ 2 + frobNormSq DC / γ ^ 2 := by
    unfold frobNormSq; simp_rw [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsum] at hle
  -- ‖DA‖²/α² ≤ (ηα)²/α² = η², etc.
  have hα2 : (0 : ℝ) < α ^ 2 := sq_pos_of_pos hα
  have hβ2 : (0 : ℝ) < β ^ 2 := sq_pos_of_pos hβ
  have hγ2 : (0 : ℝ) < γ ^ 2 := sq_pos_of_pos hγ
  have h1 : frobNormSq DA / α ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hα2]; nlinarith
  have h2 : frobNormSq DB / β ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hβ2]; nlinarith
  have h3 : frobNormSq DC / γ ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hγ2]; nlinarith
  linarith

/-- Higham, 2nd ed., Chapter 16.2:
    original-coordinate Sylvester perturbation residual
    `DeltaA * Y - Y * DeltaB - DeltaC`. -/
noncomputable def sylvesterBackwardResidual (n : ℕ)
    (DA DB DC Y : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n DA Y i j - matMul n Y DB i j - DC i j

/-- The `IsSVD` representation is the diagonal matrix identity
    `Y = U * diag(sigma) * V^T` in the repository matrix product. -/
theorem isSVD_eq_matMul_diag (n : ℕ)
    (Y U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (hSVD : IsSVD n Y U V σ) :
    Y = matMul n U (matMul n (diagMatrix σ) (matTranspose V)) := by
  have hdiag :
      matMul n (diagMatrix σ) (matTranspose V) =
        fun k j => σ k * V j k := by
    ext k j
    rw [matMul_diagMatrix_left σ (matTranspose V) k j]
    rfl
  ext i j
  rw [hdiag]
  exact hSVD.2.2.1 i j

/-- The SVD residual transform distributes over the `M - N - P` matrix
    combination used in the Sylvester perturbation residual. -/
theorem svdResidual_sub_sub (n : ℕ)
    (U V M N P : Fin n → Fin n → ℝ) :
    svdResidual n U V (fun i j => M i j - N i j - P i j) =
      fun i j => svdResidual n U V M i j -
        svdResidual n U V N i j -
          svdResidual n U V P i j := by
  ext i j
  unfold svdResidual matMul matTranspose
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_add, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- In SVD coordinates, the left perturbation product becomes
    `DeltaA_tilde * diag(sigma)`. -/
theorem svdResidual_mul_svd_right (n : ℕ)
    (U V DA : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    svdResidual n U V
      (matMul n DA (matMul n U (matMul n (diagMatrix σ) (matTranspose V)))) =
        matMul n (matMul n (matMul n (matTranspose U) DA) U) (diagMatrix σ) := by
  unfold svdResidual
  have hVtV : matMul n (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hV.left_inv i j
  simp [matMul_assoc, hVtV, matMul_id_right]

/-- In SVD coordinates, the right perturbation product becomes
    `diag(sigma) * DeltaB_tilde`. -/
theorem svdResidual_svd_left_mul (n : ℕ)
    (U V DB : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    svdResidual n U V
      (matMul n (matMul n U (matMul n (diagMatrix σ) (matTranspose V))) DB) =
        matMul n (diagMatrix σ)
          (matMul n (matMul n (matTranspose V) DB) V) := by
  unfold svdResidual
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  calc
    matMul n (matMul n (matTranspose U)
        (matMul n (matMul n U (matMul n (diagMatrix σ) (matTranspose V))) DB)) V
        = matMul n (matMul n (matMul n (matTranspose U) U)
            (matMul n (matMul n (diagMatrix σ) (matTranspose V)) DB)) V := by
            rw [matMul_assoc n U (matMul n (diagMatrix σ) (matTranspose V)) DB]
            rw [(matMul_assoc n (matTranspose U) U
              (matMul n (matMul n (diagMatrix σ) (matTranspose V)) DB)).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n (matMul n (diagMatrix σ) (matTranspose V)) DB)) V := by
            rw [hUtU]
    _ = matMul n (matMul n (matMul n (diagMatrix σ) (matTranspose V)) DB) V := by
            rw [matMul_id_left]
    _ = matMul n (diagMatrix σ)
            (matMul n (matMul n (matTranspose V) DB) V) := by
            rw [matMul_assoc n (diagMatrix σ) (matTranspose V) DB]
            rw [matMul_assoc n (diagMatrix σ)
              (matMul n (matTranspose V) DB) V]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.13):
    transforming the original perturbation residual through an SVD of `Y`
    yields the uncoupled SVD-coordinate residual equations. -/
theorem svdResidual_backwardResidual (n : ℕ)
    (Y U V DA DB DC : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (hSVD : IsSVD n Y U V σ) :
    svdResidual n U V (sylvesterBackwardResidual n DA DB DC Y) =
      fun i j =>
        matMul n (matMul n (matTranspose U) DA) U i j * σ j -
          σ i * matMul n (matMul n (matTranspose V) DB) V i j -
            svdResidual n U V DC i j := by
  have hY := isSVD_eq_matMul_diag n Y U V σ hSVD
  unfold sylvesterBackwardResidual
  rw [hY]
  rw [svdResidual_sub_sub n U V
    (matMul n DA (matMul n U (matMul n (diagMatrix σ) (matTranspose V))))
    (matMul n (matMul n U (matMul n (diagMatrix σ) (matTranspose V))) DB)
    DC]
  rw [svdResidual_mul_svd_right n U V DA σ hSVD.2.1]
  rw [svdResidual_svd_left_mul n U V DB σ hSVD.1]
  ext i j
  rw [matMul_diagMatrix_right
    (matMul n (matMul n (matTranspose U) DA) U) σ i j]
  rw [matMul_diagMatrix_left σ
    (matMul n (matMul n (matTranspose V) DB) V) i j]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), lower direction:
    an original-coordinate perturbation residual feasible at cost `eta`
    implies the SVD-coordinate `xi^2` cost is bounded by `3 * eta^2`. -/
theorem xiSq_le_three_eta_sq_of_original_residual (n : ℕ)
    (Y R U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ η : ℝ) (DA DB DC : Fin n → Fin n → ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)
    (hResidual : sylvesterBackwardResidual n DA DB DC Y = R)
    (hDA : frobNormSq DA ≤ (η * α) ^ 2)
    (hDB : frobNormSq DB ≤ (η * β) ^ 2)
    (hDC : frobNormSq DC ≤ (η * γ) ^ 2) :
    xiSq n (svdResidual n U V R) σ α β γ ≤ 3 * η ^ 2 := by
  have hbridge := svdResidual_backwardResidual n Y U V DA DB DC σ hSVD
  have hmat :
      svdResidual n U V R =
        fun i j =>
          matMul n (matMul n (matTranspose U) DA) U i j * σ j -
            σ i * matMul n (matMul n (matTranspose V) DB) V i j -
              svdResidual n U V DC i j := by
    rw [← hResidual]
    exact hbridge
  have hEq : ∀ i j : Fin n,
      matMul n (matMul n (matTranspose U) DA) U i j * σ j -
          σ i * matMul n (matMul n (matTranspose V) DB) V i j -
            svdResidual n U V DC i j =
        svdResidual n U V R i j := by
    intro i j
    exact (congrFun (congrFun hmat i) j).symm
  have hDAnorm :
      frobNormSq (matMul n (matMul n (matTranspose U) DA) U) =
        frobNormSq DA := by
    rw [frobNormSq_orthogonal_right _ _ hSVD.1,
      frobNormSq_orthogonal_left _ _ hSVD.1.transpose]
  have hDBnorm :
      frobNormSq (matMul n (matMul n (matTranspose V) DB) V) =
        frobNormSq DB := by
    rw [frobNormSq_orthogonal_right _ _ hSVD.2.1,
      frobNormSq_orthogonal_left _ _ hSVD.2.1.transpose]
  have hDCnorm :
      frobNormSq (svdResidual n U V DC) = frobNormSq DC :=
    svdResidual_frobNormSq n U V DC hSVD.1 hSVD.2.1
  exact backward_error_eta_bound n (svdResidual n U V R) σ α β γ η
    hα hβ hγ
    (matMul n (matMul n (matTranspose U) DA) U)
    (matMul n (matMul n (matTranspose V) DB) V)
    (svdResidual n U V DC)
    hpos hEq
    (by rwa [hDAnorm])
    (by rwa [hDBnorm])
    (by rwa [hDCnorm])

/-- Higham, 2nd ed., Chapter 16.2, equations (16.10), (16.13), and (16.15):
    every square Frobenius backward-error certificate at cost `eta` gives the
    SVD-coordinate lower-bound inequality `xi^2 <= 3 * eta^2`. -/
theorem xiSq_le_three_eta_sq_of_backward_error (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ η : ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hBack : IsBackwardError n A B C Y α β γ η)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    xiSq n (svdResidual n U V (sylvesterResidual n A B C Y)) σ α β γ ≤
      3 * η ^ 2 := by
  rcases hBack with ⟨DA, DB, DC, hEq, hDA, hDB, hDC⟩
  have hResidualPoint := residual_decomposition n A B C Y DA DB DC hEq
  have hResidual :
      sylvesterBackwardResidual n DA DB DC Y =
        sylvesterResidual n A B C Y := by
    ext i j
    unfold sylvesterBackwardResidual
    exact (hResidualPoint i j).symm
  exact xiSq_le_three_eta_sq_of_original_residual n Y
    (sylvesterResidual n A B C Y) U V σ α β γ η DA DB DC
    hSVD hα hβ hγ hpos hResidual hDA hDB hDC

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    lift an SVD-coordinate `DeltaA` perturbation back to original coordinates. -/
noncomputable def svdLiftDeltaA (n : ℕ)
    (U DA_tilde : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n U (matMul n DA_tilde (matTranspose U))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    lift an SVD-coordinate `DeltaB` perturbation back to original coordinates. -/
noncomputable def svdLiftDeltaB (n : ℕ)
    (V DB_tilde : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n V (matMul n DB_tilde (matTranspose V))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    lift an SVD-coordinate `DeltaC` perturbation back to original coordinates. -/
noncomputable def svdLiftDeltaC (n : ℕ)
    (U V DC_tilde : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n U (matMul n DC_tilde (matTranspose V))

/-- The lifted `DeltaA` returns to the original SVD-coordinate perturbation
    after conjugation by the left singular-vector basis. -/
theorem svdLiftDeltaA_svd_coordinates (n : ℕ)
    (U DA_tilde : Fin n → Fin n → ℝ) (hU : IsOrthogonal n U) :
    matMul n (matMul n (matTranspose U) (svdLiftDeltaA n U DA_tilde)) U =
      DA_tilde := by
  unfold svdLiftDeltaA
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  calc
    matMul n (matMul n (matTranspose U)
        (matMul n U (matMul n DA_tilde (matTranspose U)))) U
        = matMul n (matMul n (matMul n (matTranspose U) U)
            (matMul n DA_tilde (matTranspose U))) U := by
            rw [(matMul_assoc n (matTranspose U) U
              (matMul n DA_tilde (matTranspose U))).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n DA_tilde (matTranspose U))) U := by
            rw [hUtU]
    _ = matMul n (matMul n DA_tilde (matTranspose U)) U := by
            rw [matMul_id_left]
    _ = matMul n DA_tilde (matMul n (matTranspose U) U) := by
            rw [matMul_assoc]
    _ = matMul n DA_tilde (idMatrix n) := by
            rw [hUtU]
    _ = DA_tilde := by
            rw [matMul_id_right]

/-- The lifted `DeltaB` returns to the original SVD-coordinate perturbation
    after conjugation by the right singular-vector basis. -/
theorem svdLiftDeltaB_svd_coordinates (n : ℕ)
    (V DB_tilde : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V) :
    matMul n (matMul n (matTranspose V) (svdLiftDeltaB n V DB_tilde)) V =
      DB_tilde := by
  unfold svdLiftDeltaB
  have hVtV : matMul n (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hV.left_inv i j
  calc
    matMul n (matMul n (matTranspose V)
        (matMul n V (matMul n DB_tilde (matTranspose V)))) V
        = matMul n (matMul n (matMul n (matTranspose V) V)
            (matMul n DB_tilde (matTranspose V))) V := by
            rw [(matMul_assoc n (matTranspose V) V
              (matMul n DB_tilde (matTranspose V))).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n DB_tilde (matTranspose V))) V := by
            rw [hVtV]
    _ = matMul n (matMul n DB_tilde (matTranspose V)) V := by
            rw [matMul_id_left]
    _ = matMul n DB_tilde (matMul n (matTranspose V) V) := by
            rw [matMul_assoc]
    _ = matMul n DB_tilde (idMatrix n) := by
            rw [hVtV]
    _ = DB_tilde := by
            rw [matMul_id_right]

/-- The lifted `DeltaC` returns to the original SVD-coordinate perturbation
    under the residual transform `U^T * DeltaC * V`. -/
theorem svdResidual_svdLiftDeltaC (n : ℕ)
    (U V DC_tilde : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    svdResidual n U V (svdLiftDeltaC n U V DC_tilde) = DC_tilde := by
  unfold svdResidual svdLiftDeltaC
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  have hVtV : matMul n (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hV.left_inv i j
  calc
    matMul n (matMul n (matTranspose U)
        (matMul n U (matMul n DC_tilde (matTranspose V)))) V
        = matMul n (matMul n (matMul n (matTranspose U) U)
            (matMul n DC_tilde (matTranspose V))) V := by
            rw [(matMul_assoc n (matTranspose U) U
              (matMul n DC_tilde (matTranspose V))).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n DC_tilde (matTranspose V))) V := by
            rw [hUtU]
    _ = matMul n (matMul n DC_tilde (matTranspose V)) V := by
            rw [matMul_id_left]
    _ = matMul n DC_tilde (matMul n (matTranspose V) V) := by
            rw [matMul_assoc]
    _ = matMul n DC_tilde (idMatrix n) := by
            rw [hVtV]
    _ = DC_tilde := by
            rw [matMul_id_right]

/-- The SVD residual transform is inverted by multiplying by `U` on the left
    and `V^T` on the right. -/
theorem svdResidual_inverse (n : ℕ)
    (U V R : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    matMul n U (matMul n (svdResidual n U V R) (matTranspose V)) = R := by
  unfold svdResidual
  have hUUt : matMul n U (matTranspose U) = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.right_inv i j
  have hVVt : matMul n V (matTranspose V) = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hV.right_inv i j
  calc
    matMul n U
        (matMul n (matMul n (matMul n (matTranspose U) R) V)
          (matTranspose V))
        = matMul n (matMul n U
            (matMul n (matMul n (matTranspose U) R) V))
          (matTranspose V) := by
            rw [(matMul_assoc n U
              (matMul n (matMul n (matTranspose U) R) V)
              (matTranspose V)).symm]
    _ = matMul n (matMul n (matMul n U (matMul n (matTranspose U) R)) V)
          (matTranspose V) := by
            rw [(matMul_assoc n U (matMul n (matTranspose U) R) V).symm]
    _ = matMul n (matMul n U (matMul n (matTranspose U) R))
          (matMul n V (matTranspose V)) := by
            rw [matMul_assoc]
    _ = matMul n (matMul n U (matMul n (matTranspose U) R))
          (idMatrix n) := by
            rw [hVVt]
    _ = matMul n U (matMul n (matTranspose U) R) := by
            rw [matMul_id_right]
    _ = matMul n (matMul n U (matTranspose U)) R := by
            rw [matMul_assoc]
    _ = matMul n (idMatrix n) R := by
            rw [hUUt]
    _ = R := by
            rw [matMul_id_left]

/-- If the lifted SVD-coordinate perturbations satisfy the transformed
    residual equation, then their original-coordinate backward residual is the
    supplied original residual. -/
theorem svdLift_backwardResidual_eq (n : ℕ)
    (Y R U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ)
    (DA_tilde DB_tilde DC_tilde : Fin n → Fin n → ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (hEq : ∀ i j : Fin n,
      DA_tilde i j * sigma j - sigma i * DB_tilde i j - DC_tilde i j =
        svdResidual n U V R i j) :
    sylvesterBackwardResidual n
        (svdLiftDeltaA n U DA_tilde)
        (svdLiftDeltaB n V DB_tilde)
        (svdLiftDeltaC n U V DC_tilde) Y = R := by
  have hcoords :
      svdResidual n U V
          (sylvesterBackwardResidual n
            (svdLiftDeltaA n U DA_tilde)
            (svdLiftDeltaB n V DB_tilde)
            (svdLiftDeltaC n U V DC_tilde) Y) =
        svdResidual n U V R := by
    rw [svdResidual_backwardResidual n Y U V
      (svdLiftDeltaA n U DA_tilde)
      (svdLiftDeltaB n V DB_tilde)
      (svdLiftDeltaC n U V DC_tilde) sigma hSVD]
    rw [svdLiftDeltaA_svd_coordinates n U DA_tilde hSVD.1]
    rw [svdLiftDeltaB_svd_coordinates n V DB_tilde hSVD.2.1]
    rw [svdResidual_svdLiftDeltaC n U V DC_tilde hSVD.1 hSVD.2.1]
    ext i j
    exact hEq i j
  calc
    sylvesterBackwardResidual n
        (svdLiftDeltaA n U DA_tilde)
        (svdLiftDeltaB n V DB_tilde)
        (svdLiftDeltaC n U V DC_tilde) Y
        = matMul n U (matMul n
            (svdResidual n U V
              (sylvesterBackwardResidual n
                (svdLiftDeltaA n U DA_tilde)
                (svdLiftDeltaB n V DB_tilde)
                (svdLiftDeltaC n U V DC_tilde) Y))
            (matTranspose V)) := by
            rw [svdResidual_inverse n U V
              (sylvesterBackwardResidual n
                (svdLiftDeltaA n U DA_tilde)
                (svdLiftDeltaB n V DB_tilde)
                (svdLiftDeltaC n U V DC_tilde) Y)
              hSVD.1 hSVD.2.1]
    _ = matMul n U (matMul n (svdResidual n U V R) (matTranspose V)) := by
            rw [hcoords]
    _ = R := by
            rw [svdResidual_inverse n U V R hSVD.1 hSVD.2.1]

/-- A residual equality `DeltaA * Y - Y * DeltaB - DeltaC = R` is the
    original-coordinate backward-error equation in the repository predicate. -/
theorem backwardError_equation_of_backwardResidual_eq (n : ℕ)
    (A B C Y DA DB DC : Fin n → Fin n → ℝ)
    (hResidual :
      sylvesterBackwardResidual n DA DB DC Y = sylvesterResidual n A B C Y) :
    ∀ i j : Fin n,
      sylvesterOp n (fun i' j' => A i' j' + DA i' j')
        (fun i' j' => B i' j' + DB i' j') Y i j = C i j + DC i j := by
  intro i j
  have h := congrFun (congrFun hResidual i) j
  unfold sylvesterBackwardResidual sylvesterResidual sylvesterOp matMul at h
  unfold sylvesterOp matMul
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at h ⊢
  linarith

/-- The original-coordinate lift preserves the squared Frobenius norm of the
    SVD-coordinate `DeltaA` perturbation. -/
theorem svdLiftDeltaA_frobNormSq (n : ℕ)
    (U DA_tilde : Fin n → Fin n → ℝ) (hU : IsOrthogonal n U) :
    frobNormSq (svdLiftDeltaA n U DA_tilde) = frobNormSq DA_tilde := by
  unfold svdLiftDeltaA
  rw [frobNormSq_orthogonal_left _ _ hU,
    frobNormSq_orthogonal_right _ _ hU.transpose]

/-- The original-coordinate lift preserves the squared Frobenius norm of the
    SVD-coordinate `DeltaB` perturbation. -/
theorem svdLiftDeltaB_frobNormSq (n : ℕ)
    (V DB_tilde : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V) :
    frobNormSq (svdLiftDeltaB n V DB_tilde) = frobNormSq DB_tilde := by
  unfold svdLiftDeltaB
  rw [frobNormSq_orthogonal_left _ _ hV,
    frobNormSq_orthogonal_right _ _ hV.transpose]

/-- The original-coordinate lift preserves the squared Frobenius norm of the
    SVD-coordinate `DeltaC` perturbation. -/
theorem svdLiftDeltaC_frobNormSq (n : ℕ)
    (U V DC_tilde : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    frobNormSq (svdLiftDeltaC n U V DC_tilde) = frobNormSq DC_tilde := by
  unfold svdLiftDeltaC
  rw [frobNormSq_orthogonal_left _ _ hU,
    frobNormSq_orthogonal_right _ _ hV.transpose]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper direction:
    the coordinatewise optimizer lifts to an original-coordinate backward-error
    certificate with cost `sqrt xiSq`.  This is the constructive eta-side
    feasibility theorem; turning it into a literal minimum/infimum statement
    for the source `eta(Y)` remains a separate order-theoretic wrapper. -/
theorem isBackwardError_sqrt_xiSq_of_svdOptimalPerturbations (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ) (alpha beta gamma : ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    IsBackwardError n A B C Y alpha beta gamma
      (Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma)) := by
  let R_tilde : Fin n → Fin n → ℝ :=
    svdResidual n U V (sylvesterResidual n A B C Y)
  let eta : ℝ := Real.sqrt (xiSq n R_tilde sigma alpha beta gamma)
  change IsBackwardError n A B C Y alpha beta gamma eta
  let DA_tilde : Fin n → Fin n → ℝ :=
    svdOptimalDeltaA n R_tilde sigma alpha beta gamma
  let DB_tilde : Fin n → Fin n → ℝ :=
    svdOptimalDeltaB n R_tilde sigma alpha beta gamma
  let DC_tilde : Fin n → Fin n → ℝ :=
    svdOptimalDeltaC n R_tilde sigma alpha beta gamma
  refine ⟨svdLiftDeltaA n U DA_tilde,
    svdLiftDeltaB n V DB_tilde,
    svdLiftDeltaC n U V DC_tilde, ?_, ?_, ?_, ?_⟩
  · have hscalar :
        ∀ i j : Fin n,
          DA_tilde i j * sigma j - sigma i * DB_tilde i j - DC_tilde i j =
            R_tilde i j := by
      exact svdOptimalPerturbations_scalar_eq n R_tilde sigma alpha beta gamma hpos
    have hResidual :
        sylvesterBackwardResidual n
          (svdLiftDeltaA n U DA_tilde)
          (svdLiftDeltaB n V DB_tilde)
          (svdLiftDeltaC n U V DC_tilde) Y =
            sylvesterResidual n A B C Y := by
      exact svdLift_backwardResidual_eq n Y (sylvesterResidual n A B C Y)
        U V sigma DA_tilde DB_tilde DC_tilde hSVD hscalar
    exact backwardError_equation_of_backwardResidual_eq n A B C Y
      (svdLiftDeltaA n U DA_tilde)
      (svdLiftDeltaB n V DB_tilde)
      (svdLiftDeltaC n U V DC_tilde) hResidual
  · have hxi : 0 ≤ xiSq n R_tilde sigma alpha beta gamma :=
      xiSq_nonneg R_tilde sigma alpha beta gamma hpos
    have hbounds :=
      svdOptimalPerturbations_frobNormSq_bounds n R_tilde sigma alpha beta gamma hpos
    rw [svdLiftDeltaA_frobNormSq n U DA_tilde hSVD.1]
    calc
      frobNormSq DA_tilde ≤ alpha ^ 2 * xiSq n R_tilde sigma alpha beta gamma := by
          simpa [DA_tilde] using hbounds.1
      _ = (eta * alpha) ^ 2 := by
          unfold eta
          rw [mul_pow, Real.sq_sqrt hxi]
          ring
  · have hxi : 0 ≤ xiSq n R_tilde sigma alpha beta gamma :=
      xiSq_nonneg R_tilde sigma alpha beta gamma hpos
    have hbounds :=
      svdOptimalPerturbations_frobNormSq_bounds n R_tilde sigma alpha beta gamma hpos
    rw [svdLiftDeltaB_frobNormSq n V DB_tilde hSVD.2.1]
    calc
      frobNormSq DB_tilde ≤ beta ^ 2 * xiSq n R_tilde sigma alpha beta gamma := by
          simpa [DB_tilde] using hbounds.2.1
      _ = (eta * beta) ^ 2 := by
          unfold eta
          rw [mul_pow, Real.sq_sqrt hxi]
          ring
  · have hxi : 0 ≤ xiSq n R_tilde sigma alpha beta gamma :=
      xiSq_nonneg R_tilde sigma alpha beta gamma hpos
    have hbounds :=
      svdOptimalPerturbations_frobNormSq_bounds n R_tilde sigma alpha beta gamma hpos
    rw [svdLiftDeltaC_frobNormSq n U V DC_tilde hSVD.1 hSVD.2.1]
    calc
      frobNormSq DC_tilde ≤ gamma ^ 2 * xiSq n R_tilde sigma alpha beta gamma := by
          simpa [DC_tilde] using hbounds.2.2
      _ = (eta * gamma) ^ 2 := by
          unfold eta
          rw [mul_pow, Real.sq_sqrt hxi]
          ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    nonnegative feasible values for the normwise Sylvester backward error
    `eta(Y)`.  The nonnegativity guard avoids the symmetric square-bound
    predicate admitting negative costs. -/
def sylvesterBackwardErrorValues (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ) : Set ℝ :=
  {eta | 0 ≤ eta ∧ IsBackwardError n A B C Y alpha beta gamma eta}

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    `eta(Y)` modeled as the infimum of the nonnegative feasible backward-error
    certificates.  This is an infimum model, not an attained-minimum claim. -/
noncomputable def sylvesterBackwardErrorInf (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ) : ℝ :=
  sInf (sylvesterBackwardErrorValues n A B C Y alpha beta gamma)

/-- The nonnegative feasible-value set for `eta(Y)` is bounded below by zero. -/
theorem sylvesterBackwardErrorValues_bddBelow (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ) :
    BddBelow (sylvesterBackwardErrorValues n A B C Y alpha beta gamma) := by
  refine ⟨0, ?_⟩
  intro eta heta
  exact heta.1

/-- The infimum model of `eta(Y)` is nonnegative because all feasible costs are
    restricted to be nonnegative. -/
theorem sylvesterBackwardErrorInf_nonneg (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ) :
    0 ≤ sylvesterBackwardErrorInf n A B C Y alpha beta gamma := by
  unfold sylvesterBackwardErrorInf sylvesterBackwardErrorValues
  apply Real.sInf_nonneg
  intro eta heta
  exact heta.1

/-- Any nonnegative backward-error certificate lies above the infimum model. -/
theorem sylvesterBackwardErrorInf_le_of_backwardError (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma eta : ℝ)
    (heta_nonneg : 0 ≤ eta)
    (hBack : IsBackwardError n A B C Y alpha beta gamma eta) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma ≤ eta := by
  unfold sylvesterBackwardErrorInf
  exact csInf_le
    (sylvesterBackwardErrorValues_bddBelow n A B C Y alpha beta gamma)
    ⟨heta_nonneg, hBack⟩

/-- The SVD optimizer supplies a nonempty feasible set for the infimum model of
    `eta(Y)`. -/
theorem sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ) (alpha beta gamma : ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    (sylvesterBackwardErrorValues n A B C Y alpha beta gamma).Nonempty := by
  refine ⟨Real.sqrt
      (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
        sigma alpha beta gamma), ?_⟩
  exact ⟨Real.sqrt_nonneg _,
    isBackwardError_sqrt_xiSq_of_svdOptimalPerturbations n A B C Y U V
      sigma alpha beta gamma hSVD hpos⟩

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), upper infimum direction:
    the infimum model of `eta(Y)` is bounded above by `sqrt xiSq`. -/
theorem sylvesterBackwardErrorInf_le_sqrt_xiSq_of_svdOptimalPerturbations (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ) (alpha beta gamma : ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma ≤
      Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma) :=
  sylvesterBackwardErrorInf_le_of_backwardError n A B C Y alpha beta gamma
    (Real.sqrt
      (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
        sigma alpha beta gamma))
    (Real.sqrt_nonneg _)
    (isBackwardError_sqrt_xiSq_of_svdOptimalPerturbations n A B C Y U V
      sigma alpha beta gamma hSVD hpos)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15), lower infimum direction:
    `sqrt (xiSq / 3)` is a lower bound for the nonnegative feasible backward
    error costs, hence it is below the infimum model of `eta(Y)`. -/
theorem sqrt_xiSq_div_three_le_sylvesterBackwardErrorInf_of_svd (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ) (alpha beta gamma : ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma / 3) ≤
      sylvesterBackwardErrorInf n A B C Y alpha beta gamma := by
  unfold sylvesterBackwardErrorInf
  apply le_csInf
    (sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations n
      A B C Y U V sigma alpha beta gamma hSVD hpos)
  intro eta heta
  rcases heta with ⟨heta_nonneg, hBack⟩
  have hle := xiSq_le_three_eta_sq_of_backward_error n A B C Y U V sigma
    alpha beta gamma eta hSVD hBack halpha hbeta hgamma hpos
  have hdiv :
      xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma / 3 ≤ eta ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heta_nonneg] at hsqrt
  exact hsqrt

/-- Higham, 2nd ed., Chapter 16.2, equation (16.17):
    infimum-model eta residual amplification bound in the square case.  The
    theorem combines the eta/xi upper bridge from (16.15) with the square-case
    `mu` residual bound from (16.17)-(16.19). -/
theorem sylvesterBackwardErrorInf_le_mu_relative_residual_of_svd (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ)
    (alpha beta gamma sigma_min : ℝ)
    (hSVD : IsSVD n Y U V sigma)
    (hsigma_min : ∀ i : Fin n, sigma_min ≤ sigma i)
    (hsigma_min_nn : 0 ≤ sigma_min)
    (hDenom : 0 < (alpha ^ 2 + beta ^ 2) * sigma_min ^ 2 + gamma ^ 2)
    (hScale : 0 < (alpha + beta) * frobNorm Y + gamma) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma ≤
      sylvesterAmplificationMuSquare alpha beta gamma (frobNorm Y) sigma_min *
        (frobNorm (sylvesterResidual n A B C Y) /
          ((alpha + beta) * frobNorm Y + gamma)) := by
  let R := sylvesterResidual n A B C Y
  let kappa :=
    sylvesterAmplificationMuSquare alpha beta gamma (frobNorm Y) sigma_min *
      (frobNorm R / ((alpha + beta) * frobNorm Y + gamma))
  have hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2 := by
    intro i j
    have hsig_i_sq : sigma_min ^ 2 ≤ sigma i ^ 2 :=
      sq_le_sq' (by linarith [hsigma_min_nn, hsigma_min i]) (hsigma_min i)
    have hsig_j_sq : sigma_min ^ 2 ≤ sigma j ^ 2 :=
      sq_le_sq' (by linarith [hsigma_min_nn, hsigma_min j]) (hsigma_min j)
    have hdenom_le :
        (alpha ^ 2 + beta ^ 2) * sigma_min ^ 2 + gamma ^ 2 ≤
          alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2 := by
      nlinarith [sq_nonneg alpha, sq_nonneg beta]
    exact lt_of_lt_of_le hDenom hdenom_le
  have heta :
      sylvesterBackwardErrorInf n A B C Y alpha beta gamma ≤
        Real.sqrt (xiSq n (svdResidual n U V R) sigma alpha beta gamma) := by
    simpa [R] using
      sylvesterBackwardErrorInf_le_sqrt_xiSq_of_svdOptimalPerturbations n
        A B C Y U V sigma alpha beta gamma hSVD hpos
  have hxi :
      xiSq n (svdResidual n U V R) sigma alpha beta gamma ≤ kappa ^ 2 := by
    simpa [R, kappa] using
      xiSq_le_mu_relative_residual_sq n Y R U V sigma alpha beta gamma sigma_min
        hSVD hsigma_min hsigma_min_nn hDenom hScale
  have hmu_nonneg :
      0 ≤ sylvesterAmplificationMuSquare alpha beta gamma (frobNorm Y) sigma_min := by
    unfold sylvesterAmplificationMuSquare
    exact div_nonneg (le_of_lt hScale) (Real.sqrt_nonneg _)
  have hrel_nonneg :
      0 ≤ frobNorm R / ((alpha + beta) * frobNorm Y + gamma) :=
    div_nonneg (frobNorm_nonneg R) (le_of_lt hScale)
  have hkappa_nonneg : 0 ≤ kappa := by
    dsimp [kappa]
    exact mul_nonneg hmu_nonneg hrel_nonneg
  have hsqrt := Real.sqrt_le_sqrt hxi
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hkappa_nonneg] at hsqrt
  exact heta.trans hsqrt

-- ============================================================
-- Residual-based backward error bound (combining eqs 16.12 + 16.16)
-- ============================================================

/-- **Combined backward error bound** (eqs 16.12 + 16.16):
    If the backward error equation holds with cost η, then
    η ≥ ‖R‖_F / ((α+β)‖Y‖_F + γ)
    (from residual_bound, rearranged). This is the easy lower bound. -/
theorem backward_error_residual_lower (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j)
    (hΔA : frobNorm ΔA ≤ η * α)
    (hΔB : frobNorm ΔB ≤ η * β)
    (hΔC : frobNorm ΔC ≤ η * γ)
    (_hd : 0 < (α + β) * frobNorm Y + γ) :
    frobNorm (sylvesterResidual n A B C Y) ≤
    ((α + β) * frobNorm Y + γ) * η := by
  exact residual_bound n A B C Y ΔA ΔB ΔC α β γ η hα hβ hγ hη hEq hΔA hΔB hΔC

-- ============================================================
-- Lyapunov spectral-coordinate backward error (§16.2.1, eq 16.21)
-- ============================================================






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
