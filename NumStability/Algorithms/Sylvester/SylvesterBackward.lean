-- Algorithms/Sylvester/SylvesterBackward.lean
--
-- SVD-based backward error analysis for the Sylvester equation (Higham §16.2).
-- Eqs 16.13-16.19: backward error characterization via SVD coordinates,
-- lower/upper bounds on η(Y), amplification factor μ, and the Lyapunov
-- scalar-coordinate and xi/mu analogues in §16.2.1.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.Sylvester.SylvesterSpec

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

/-- Higham, 2nd ed., Section 16.2, equation (16.13):
    source-numbered abbreviation for the SVD-coordinate representation. -/
abbrev H16_eq16_13_IsSVD := IsSVD

/-- Higham, 2nd ed., Section 16.2, equation (16.13):
    source-numbered abbreviation for the transformed SVD residual. -/
noncomputable abbrev H16_eq16_13_svdResidual := svdResidual

/-- Higham, 2nd ed., Section 16.2, equation (16.13):
    source-numbered alias for Frobenius-norm preservation of the transformed
    SVD residual. -/
alias H16_eq16_13_svdResidual_frobNormSq :=
  svdResidual_frobNormSq

/-- Higham, 2nd ed., Section 16.2, equation (16.16):
    source-numbered abbreviation for the squared `xi` functional. -/
noncomputable abbrev H16_eq16_16_xiSq := xiSq

/-- Higham, 2nd ed., Section 16.2, equation (16.16):
    source-numbered alias for nonnegativity of the squared `xi` functional. -/
alias H16_eq16_16_xiSq_nonneg :=
  xiSq_nonneg

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

/-- Higham, 2nd ed., Chapter 16.2, equations (16.14)-(16.15):
    source-numbered alias for the Cauchy-Schwarz lower-cost consequence of
    the uncoupled SVD-coordinate scalar equations. -/
alias H16_eq16_14_15_backward_error_lower_sq := backward_error_lower_sq

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

/-- Higham, 2nd ed., Chapter 16.2, equation (16.15):
    source-numbered aliases for the SVD-coordinate optimizer construction and
    its component squared-Frobenius bounds. -/
alias H16_eq16_15_backward_error_upper_component :=
  backward_error_upper_component

noncomputable abbrev H16_eq16_15_svdOptimalDeltaA := svdOptimalDeltaA

noncomputable abbrev H16_eq16_15_svdOptimalDeltaB := svdOptimalDeltaB

noncomputable abbrev H16_eq16_15_svdOptimalDeltaC := svdOptimalDeltaC

alias H16_eq16_15_svdOptimalPerturbations_scalar_eq :=
  svdOptimalPerturbations_scalar_eq

alias H16_eq16_15_svdOptimalPerturbations_cost_eq_xiSq :=
  svdOptimalPerturbations_cost_eq_xiSq

alias H16_eq16_15_exists_svdOptimalPerturbations :=
  exists_svdOptimalPerturbations

alias H16_eq16_15_svdOptimalDeltaA_frobNormSq_le_xiSq :=
  svdOptimalDeltaA_frobNormSq_le_xiSq

alias H16_eq16_15_svdOptimalDeltaB_frobNormSq_le_xiSq :=
  svdOptimalDeltaB_frobNormSq_le_xiSq

alias H16_eq16_15_svdOptimalDeltaC_frobNormSq_le_xiSq :=
  svdOptimalDeltaC_frobNormSq_le_xiSq

alias H16_eq16_15_svdOptimalPerturbations_frobNormSq_bounds :=
  svdOptimalPerturbations_frobNormSq_bounds

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

/-- Higham, 2nd ed., Chapter 16.2, equation (16.18):
    source-numbered abbreviation for the scalar amplification factor. -/
noncomputable abbrev H16_eq16_18_sylvesterAmplificationMu :=
  sylvesterAmplificationMu

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19):
    square-case specialization of the amplification factor. -/
noncomputable def sylvesterAmplificationMuSquare
    (α β γ yNorm σmin : ℝ) : ℝ :=
  ((α + β) * yNorm + γ) /
    Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19):
    source-numbered abbreviation for the square-case amplification factor. -/
noncomputable abbrev H16_eq16_19_sylvesterAmplificationMuSquare :=
  sylvesterAmplificationMuSquare

/-- In the square case, the two singular-value slots in (16.18) coincide,
    giving the source formula (16.19). -/
theorem sylvesterAmplificationMu_square_eq
    (α β γ yNorm σmin : ℝ) :
    sylvesterAmplificationMu α β γ yNorm σmin σmin =
      sylvesterAmplificationMuSquare α β γ yNorm σmin := by
  unfold sylvesterAmplificationMu sylvesterAmplificationMuSquare
  rw [show α ^ 2 * σmin ^ 2 + β ^ 2 * σmin ^ 2 + γ ^ 2 =
      (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2 by ring]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19): source-numbered
    alias for the square-case reduction of the amplification factor. -/
alias H16_eq16_19_sylvesterAmplificationMu_square_eq :=
  sylvesterAmplificationMu_square_eq

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

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19) and following prose:
    source-numbered alias for the square-case lower bound `1 <= mu`. -/
alias H16_eq16_19_one_le_sylvesterAmplificationMuSquare :=
  one_le_sylvesterAmplificationMuSquare

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

/-- Higham, 2nd ed., Chapter 16.2, equations (16.17)-(16.18):
    source-numbered alias for the SVD-coordinate xi-squared amplification
    bound from a uniform lower bound on the singular-value slots. -/
alias H16_eq16_17_18_xiSq_amplification_bound :=
  xiSq_amplification_bound

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19):
    source-numbered alias for the square orthogonal-invariance form of the
    xi-squared amplification bound. -/
alias H16_eq16_17_19_amplification_factor_bound :=
  amplification_factor_bound

/-- Higham, 2nd ed., Chapter 16.2, equations (16.17)-(16.19):
    source-numbered alias for the xi-squared bound written with the square
    amplification factor and the relative residual. -/
alias H16_eq16_17_19_xiSq_le_mu_relative_residual_sq :=
  xiSq_le_mu_relative_residual_sq

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

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered abbreviation for the structured Lyapunov backward
    residual. -/
noncomputable abbrev H16_eq16_21_lyapunovBackwardResidual :=
  lyapunovBackwardResidual

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

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered abbreviation for the structured Lyapunov eta feasible set. -/
abbrev H16_eq16_21_lyapunovBackwardErrorValues :=
  lyapunovBackwardErrorValues

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered abbreviation for the structured Lyapunov eta infimum. -/
noncomputable abbrev H16_eq16_21_lyapunovBackwardErrorInf :=
  lyapunovBackwardErrorInf

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

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered aliases for basic structured Lyapunov eta-infimum facts. -/
alias H16_eq16_21_lyapunovBackwardErrorValues_bddBelow :=
  lyapunovBackwardErrorValues_bddBelow

alias H16_eq16_21_lyapunovBackwardErrorInf_nonneg :=
  lyapunovBackwardErrorInf_nonneg

alias H16_eq16_21_lyapunovBackwardErrorInf_le_of_backwardError :=
  lyapunovBackwardErrorInf_le_of_backwardError

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

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered aliases for the structured Lyapunov residual decomposition
    and eta/residual bounds. -/
alias H16_eq16_21_lyapunovResidual_decomposition :=
  lyapunovResidual_decomposition

alias H16_eq16_21_lyapunov_residual_bound_of_backward_error :=
  lyapunov_residual_bound_of_backward_error

alias H16_eq16_21_lyapunov_relative_residual_le_backwardErrorInf :=
  lyapunov_relative_residual_le_backwardErrorInf

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

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered aliases for the Lyapunov scalar equation, xi/optimizer
    layer, and residual-amplification consequences. -/
abbrev H16_eq16_21_lyapunovBackwardScalarEq := lyapunovBackwardScalarEq

alias H16_eq16_21_lyapunovBackwardScalarEq_iff_unscaled :=
  lyapunovBackwardScalarEq_iff_unscaled

alias H16_eq16_21_lyapunovBackwardScalarEq_iff_residual_eq :=
  lyapunovBackwardScalarEq_iff_residual_eq

alias H16_eq16_21_lyapunovBackwardScalarEq_of_spectral_decomposition :=
  lyapunovBackwardScalarEq_of_spectral_decomposition

alias H16_eq16_21_lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition :=
  lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition

alias H16_eq16_21_lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition_symm :=
  lyapunovBackwardScalarEq_of_isLyapunovBackwardError_spectral_decomposition_symm

alias H16_eq16_21_lyapunovBackwardScalarEq_iff_diagMatrix_eq :=
  lyapunovBackwardScalarEq_iff_diagMatrix_eq

noncomputable abbrev H16_eq16_21_lyapunovXiSq := lyapunovXiSq

noncomputable abbrev H16_eq16_21_lyapunovXiSqSimpleBound :=
  lyapunovXiSqSimpleBound

noncomputable abbrev H16_eq16_21_lyapunovOptimalDeltaA :=
  lyapunovOptimalDeltaA

noncomputable abbrev H16_eq16_21_lyapunovOptimalDeltaC :=
  lyapunovOptimalDeltaC

alias H16_eq16_21_lyapunovXiSq_nonneg := lyapunovXiSq_nonneg

alias H16_eq16_21_lyapunovOptimalPerturbations_scalar_eq :=
  lyapunovOptimalPerturbations_scalar_eq

alias H16_eq16_21_lyapunovOptimalDeltaC_symmetric :=
  lyapunovOptimalDeltaC_symmetric

alias H16_eq16_21_lyapunovOptimalDeltaA_frobNormSq_le_xiSq :=
  lyapunovOptimalDeltaA_frobNormSq_le_xiSq

alias H16_eq16_21_lyapunovOptimalDeltaC_frobNormSq_le_xiSq :=
  lyapunovOptimalDeltaC_frobNormSq_le_xiSq

alias H16_eq16_21_exists_lyapunovOptimalPerturbations :=
  exists_lyapunovOptimalPerturbations

alias H16_eq16_21_isLyapunovBackwardError_sqrt_lyapunovXiSq_of_spectral_optimalPerturbations :=
  isLyapunovBackwardError_sqrt_lyapunovXiSq_of_spectral_optimalPerturbations

alias H16_eq16_21_isLyapunovBackwardError_sqrt_lyapunovXiSq_of_symmetric_spectral :=
  isLyapunovBackwardError_sqrt_lyapunovXiSq_of_symmetric_spectral

alias H16_eq16_21_lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral :=
  lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral

alias H16_eq16_21_lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral :=
  lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral

alias H16_eq16_21_two_mul_lyapunovXiSq_eq_simple_bound_of_symmetric :=
  two_mul_lyapunovXiSq_eq_simple_bound_of_symmetric

alias H16_eq16_21_lyapunovXiSqSimpleBound_le_scaled_perturbation_cost :=
  lyapunovXiSqSimpleBound_le_scaled_perturbation_cost

alias H16_eq16_21_lyapunovXiSq_le_two_eta_sq_of_scalar_eq :=
  lyapunovXiSq_le_two_eta_sq_of_scalar_eq

alias H16_eq16_21_lyapunovXiSq_le_two_eta_sq_of_backward_error_spectral :=
  lyapunovXiSq_le_two_eta_sq_of_backward_error_spectral

alias H16_eq16_21_sqrt_lyapunovXiSq_div_two_le_lyapunovBackwardErrorInf_of_symmetric_spectral :=
  sqrt_lyapunovXiSq_div_two_le_lyapunovBackwardErrorInf_of_symmetric_spectral

alias H16_eq16_21_lyapunovXiSq_le_simple_bound :=
  lyapunovXiSq_le_simple_bound

noncomputable abbrev H16_eq16_21_lyapunovAmplificationMu :=
  lyapunovAmplificationMu

alias H16_eq16_21_lyapunovXiSqSimpleBound_le_min_eigen_bound :=
  lyapunovXiSqSimpleBound_le_min_eigen_bound

alias H16_eq16_21_lyapunovXiSq_le_min_eigen_bound :=
  lyapunovXiSq_le_min_eigen_bound

alias H16_eq16_21_lyapunovXiSq_symmetric_le_min_eigen_bound :=
  lyapunovXiSq_symmetric_le_min_eigen_bound

alias H16_eq16_21_lyapunovXiSq_spectral_le_min_eigen_bound :=
  lyapunovXiSq_spectral_le_min_eigen_bound

alias H16_eq16_21_lyapunovXiSq_spectral_symmetric_le_min_eigen_bound :=
  lyapunovXiSq_spectral_symmetric_le_min_eigen_bound

alias H16_eq16_21_lyapunovXiSq_le_mu_relative_residual_sq :=
  lyapunovXiSq_le_mu_relative_residual_sq

alias H16_eq16_21_sqrt_lyapunovXiSq_le_mu_relative_residual :=
  sqrt_lyapunovXiSq_le_mu_relative_residual

end NumStability
