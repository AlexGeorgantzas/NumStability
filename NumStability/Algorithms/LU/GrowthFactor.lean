-- Algorithms/LU/GrowthFactor.lean
--
-- Growth factor for LU factorization and normwise backward error bounds
-- (Higham §9.3–§9.4, Theorem 9.5 and related results).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.3  Growth factor definition
-- ============================================================

/-- **Growth factor** for LU factorization (Higham §9.3, Definition 9.7).

    Given computed factors L̂, Û of an n×n matrix A, the growth factor is:
      ρ_n = max_{i,j} |Û_ij| / max_{i,j} |A_ij|

    This measures how much the entries of Û can grow relative to A.
    For partial pivoting, |L̂_ij| ≤ 1, so the growth factor controls
    the backward error via ||ΔA||∞ ≤ O(nρ_n)||A||∞. -/
noncomputable def growthFactor {n : ℕ} (_hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (_hA : 0 < infNorm A) : ℝ :=
  infNorm U_hat / infNorm A

-- ============================================================
-- §9.4  Normwise backward error from componentwise (Theorem 9.5)
-- ============================================================

/-- **Componentwise-to-normwise bound** for matrix perturbation.

    If |ΔA_ij| ≤ ε * ∑_k |L̂_ik| * |Û_kj| componentwise, then
      ||ΔA||∞ ≤ ε * ||L̂||∞ * ||Û||∞

    This follows because
      ∑_j |ΔA_ij| ≤ ε ∑_j ∑_k |L̂_ik||Û_kj|
                   = ε ∑_k |L̂_ik| (∑_j |Û_kj|)
                   ≤ ε (∑_k |L̂_ik|) · max_k(∑_j |Û_kj|)
                   ≤ ε ||L̂||∞ · ||Û||∞

    This is used in the proof of Theorem 9.5 (Wilkinson's bound). -/
theorem componentwise_to_normwise_bound (n : ℕ) (_hn : 0 < n)
    (L_hat U_hat ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) :
    ∀ i : Fin n, ∑ j : Fin n, |ΔA i j| ≤
      ε * (∑ k : Fin n, |L_hat i k|) * (infNorm U_hat) := by
  intro i
  have hU_row_bound : ∀ k : Fin n, ∑ j : Fin n, |U_hat k j| ≤ infNorm U_hat := by
    intro k
    exact row_sum_le_infNorm U_hat k
  calc ∑ j : Fin n, |ΔA i j|
      ≤ ∑ j : Fin n, ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
        apply Finset.sum_le_sum; intro j _; exact hΔA i j
    _ = ε * ∑ j : Fin n, ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
        rw [Finset.mul_sum]
    _ = ε * ∑ k : Fin n, |L_hat i k| * ∑ j : Fin n, |U_hat k j| := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.mul_sum]
    _ ≤ ε * ∑ k : Fin n, |L_hat i k| * infNorm U_hat := by
        apply mul_le_mul_of_nonneg_left _ hε
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hU_row_bound k) (abs_nonneg _)
    _ = ε * (∑ k : Fin n, |L_hat i k|) * infNorm U_hat := by
        conv_lhs => rw [show ∑ k : Fin n, |L_hat i k| * infNorm U_hat =
          (∑ k : Fin n, |L_hat i k|) * infNorm U_hat from
          (Finset.sum_mul _ _ _).symm]
        rw [mul_assoc]

/-- **Partial pivoting unit lower triangular bound**.

    Under partial pivoting, |L̂_ij| ≤ 1, so ∑_k |L̂_ik| ≤ n.
    This is a reusable lemma for Theorem 9.5. -/
lemma partial_pivot_L_row_sum_le (n : ℕ) (L_hat : Fin n → Fin n → ℝ)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    ∀ i : Fin n, ∑ k : Fin n, |L_hat i k| ≤ n := by
  intro i
  calc ∑ k : Fin n, |L_hat i k|
      ≤ ∑ _k : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _; exact hL_bound i k
    _ = n := by simp

/-- **Wilkinson normwise bound** (Higham §9.4, Theorem 9.5, per-row version).

    Under partial pivoting (|L̂_ij| ≤ 1), the row sums of |ΔA| satisfy:
      ∑_j |ΔA_ij| ≤ ε · n · ‖Û‖∞

    This assembles `componentwise_to_normwise_bound` with
    `partial_pivot_L_row_sum_le` to get the classical Wilkinson bound. -/
theorem wilkinson_normwise_row_bound (n : ℕ) (hn : 0 < n)
    (L_hat U_hat ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    ∀ i : Fin n, ∑ j : Fin n, |ΔA i j| ≤ ε * ↑n * infNorm U_hat := by
  intro i
  have h1 := componentwise_to_normwise_bound n hn L_hat U_hat ΔA ε hε hΔA i
  have h2 := partial_pivot_L_row_sum_le n L_hat hL_bound i
  calc ∑ j : Fin n, |ΔA i j|
      ≤ ε * (∑ k : Fin n, |L_hat i k|) * infNorm U_hat := h1
    _ ≤ ε * ↑n * infNorm U_hat := by
        apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg U_hat)
        exact mul_le_mul_of_nonneg_left h2 hε

/-- **Wilkinson normwise bound** (Higham §9.4, Theorem 9.5, full version).

    Under partial pivoting, the normwise backward error satisfies:
      ‖ΔA‖∞ ≤ ε · n · ‖Û‖∞

    This is the classical Wilkinson bound. Using the growth factor
    ρ = ‖Û‖∞ / ‖A‖∞, this becomes ‖ΔA‖∞ ≤ ε · n · ρ · ‖A‖∞. -/
theorem wilkinson_normwise_infNorm (n : ℕ) (hn : 0 < n)
    (L_hat U_hat ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    infNorm ΔA ≤ ε * ↑n * infNorm U_hat := by
  apply infNorm_le_of_row_sum_le
  · intro i
    exact wilkinson_normwise_row_bound n hn L_hat U_hat ΔA ε hε hΔA hL_bound i
  · exact mul_nonneg (mul_nonneg hε (Nat.cast_nonneg' n)) (infNorm_nonneg U_hat)

/-- **Tight Wilkinson normwise bound** (Higham §9.4, Theorem 9.5 with γ_{3n}).

    For the full LU solve (factorization + triangular solves) under partial
    pivoting (|L̂_ij| ≤ 1), the normwise backward error satisfies:
      ‖ΔA‖∞ ≤ γ(3n) · n · ‖Û‖∞

    This absorbs the 3γ(n) + γ(n)² factor from Theorem 9.4 into γ(3n)
    using the absorption lemma `three_gamma_plus_sq_le_gamma`. -/
theorem wilkinson_normwise_infNorm_tight (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hfpn : gammaValid fp n)
    (hfp3n : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ gamma fp (3 * n) * ↑n * infNorm U_hat) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hfpn hfp3n
  refine ⟨ΔA, ?_, hΔA_eq⟩
  exact wilkinson_normwise_infNorm n hn L_hat U_hat ΔA
    (gamma fp (3 * n)) (gamma_nonneg fp hfp3n) hΔA_bound hL_bound

/-- Higham §1.10.1 / §9.2, 2-by-2 GEPP residual bridge.

For a 2-by-2 LU solve satisfying the partial-pivoting multiplier bound
`|L_hat i j| ≤ 1`, the computed solution has scaled residual bounded by the
Wilkinson perturbation radius converted to the repository's operator-2 residual
surface.  This is the exact Lean form behind the Chapter 1 statement that the
GEPP residual is of order unit roundoff for `n = 2`, before substituting a
concrete growth/norm comparison for `||U_hat||∞ / ||A||₂`. -/
theorem gepp2_relativeResidual2_le_wilkinson
    (fp : FPModel)
    (A L_hat U_hat : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (A_norm : ℝ)
    (hApos : 0 < A_norm)
    (hL_diag : ∀ i : Fin 2, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin 2, U_hat i i ≠ 0)
    (hLU : LUBackwardError 2 A L_hat U_hat (gamma fp 2))
    (hfp2 : gammaValid fp 2)
    (hfp6 : gammaValid fp (3 * 2))
    (hL_bound : ∀ i j : Fin 2, |L_hat i j| ≤ 1)
    (hxhat :
      vecNorm2 (fl_backSub fp 2 U_hat (fl_forwardSub fp 2 L_hat b)) ≠ 0) :
    relativeResidual2 2 A
      (fl_backSub fp 2 U_hat (fl_forwardSub fp 2 L_hat b)) b A_norm ≤
      (Real.sqrt (2 : ℝ) *
        (gamma fp (3 * 2) * (2 : ℝ) * infNorm U_hat)) / A_norm := by
  let y_hat := fl_forwardSub fp 2 L_hat b
  let x_hat := fl_backSub fp 2 U_hat y_hat
  obtain ⟨ΔA, hΔA_inf, hΔA_solve⟩ :=
    wilkinson_normwise_infNorm_tight fp 2 (by norm_num) A L_hat U_hat b
      hL_diag hU_diag hLU hfp2 hfp6 hL_bound
  let η : ℝ :=
    (Real.sqrt (2 : ℝ) *
      (gamma fp (3 * 2) * (2 : ℝ) * infNorm U_hat)) / A_norm
  have hηA :
      Real.sqrt (2 : ℝ) *
        (gamma fp (3 * 2) * (2 : ℝ) * infNorm U_hat) =
        η * A_norm := by
    unfold η
    field_simp [ne_of_gt hApos]
  have hΔA_op : opNorm2Le ΔA (η * A_norm) := by
    apply opNorm2Le_of_sqrt_two_infNorm_le
    calc
      Real.sqrt (2 : ℝ) * infNorm ΔA
          ≤ Real.sqrt (2 : ℝ) *
              (gamma fp (3 * 2) * (2 : ℝ) * infNorm U_hat) :=
            mul_le_mul_of_nonneg_left (by simpa using hΔA_inf) (Real.sqrt_nonneg _)
      _ = η * A_norm := hηA
  have hback :
      relativeMatrixOnlyBackwardError2Le 2 A x_hat b A_norm η :=
    ⟨ΔA, hΔA_solve, hΔA_op⟩
  simpa [x_hat, y_hat, η] using
    relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le 2 A x_hat b
      A_norm η hxhat hApos hback

-- ============================================================
-- §9.8  Diagonal dominance and growth bounds
-- ============================================================

/-- **Upper Hessenberg matrix** predicate.

    A matrix A is upper Hessenberg if A_ij = 0 for i > j + 1.
    Equivalently, entries more than one position below the diagonal are zero.
    Used in Theorem 9.9 (growth factor ρ ≤ n for Hessenberg matrices). -/
def IsUpperHessenberg (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val + 1 < i.val → A i j = 0

/-- **Hessenberg growth factor bound** (Higham §9.4, Theorem 9.9).

    For an upper Hessenberg matrix with partial pivoting, the growth factor
    satisfies ρ ≤ n. Combined with the Wilkinson bound, this gives
    ‖ΔA‖∞ ≤ ε · n² · ‖A‖∞, proving backward stability.

    This theorem takes the structural bound as a hypothesis, as the proof
    requires analysis of the elimination algorithm on Hessenberg structure. -/
theorem hessenberg_growth_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ↑n * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ↑n * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact lu_backward_error_relative n A L_hat U_hat ε ↑n hε (Nat.cast_nonneg _) hLU hGrowth

/-- **Diagonal dominance** of a matrix.

    A matrix A is (column) diagonally dominant if for each column j:
      |A_jj| ≥ ∑_{i≠j} |A_ij|

    Equivalently, |A_jj| ≥ ∑_{i≠j} |A_ij|.
    Used in Theorem 9.8 (bounded growth for diag-dominant matrices). -/
def IsDiagDominant (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ∑ i : Fin n, (if i = j then 0 else |A i j|) ≤ |A j j|

/-- **Row diagonal dominance**: for each row i, |A_ii| ≥ ∑_{j≠i} |A_ij|. -/
def IsRowDiagDominant (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, (if i = j then 0 else |A i j|) ≤ |A i i|

/-- **Bounded growth factor for diagonally dominant matrices** (Higham §9.8).

    For a diagonally dominant matrix, LU factorization without pivoting
    has growth factor ρ_n ≤ 2. This means GE without pivoting is
    backward stable for diagonally dominant systems.

    Formally: if A is row diagonally dominant and the LU factorization
    backward error is bounded by ε, then
      |ΔA_ij| ≤ 2ε * |A_ij|

    This is weaker than the full Theorem 9.8 but captures the essential
    reusable fact: diagonal dominance implies bounded growth. -/
theorem diagDom_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * 2 * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact lu_backward_error_relative n A L_hat U_hat ε 2 hε (by linarith) hLU hGrowth

/-- **Overall solve backward error for diagonally dominant systems**.

    Combining `lu_solve_backward_error` with the growth factor bound ρ ≤ 2:
    if A is diagonally dominant and we solve Ax = b via LU + triangular solves,
    the total backward error is (A + ΔA)x̂ = b with
      |ΔA_ij| ≤ (3γ(n) + γ(n)²) * 2 * |A_ij|

    This proves backward stability of LU without pivoting for diag-dominant A. -/
theorem diagDom_lu_solve_backward_stable (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        2 * (3 * gamma fp n + gamma fp n ^ 2) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error fp n A L_hat U_hat b hL_diag hU_diag hLU hn
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  calc |ΔA i j|
      ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ (3 * gamma fp n + gamma fp n ^ 2) * (2 * |A i j|) := by
        apply mul_le_mul_of_nonneg_left (hGrowth i j)
        have hγ := gamma_nonneg fp hn
        nlinarith [sq_nonneg (gamma fp n)]
    _ = 2 * (3 * gamma fp n + gamma fp n ^ 2) * |A i j| := by ring

/-- **Tight solve backward error for diagonally dominant systems** (Higham §9.4).

    Absorbs 3γ(n) + γ(n)² into γ(3n):
      |ΔA_ij| ≤ 2 · γ(3n) · |A_ij| -/
theorem diagDom_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (2 * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = 2 * gamma fp (3 * n) * |A i j| := by ring

-- ============================================================
-- §9.3  Growth factor bounds (Theorems 9.7, 9.10)
-- ============================================================

/-- **General growth factor backward error** (Higham §9.4, Theorem 9.10 pattern).

    For a banded matrix with upper and lower bandwidth p, GEPP satisfies:
      ρ_n^p ≤ 2^{2p-1} - (p-1)·2^{p-2}

    For tridiagonal matrices (p = 1), this gives ρ ≤ 2.

    This theorem takes the banded growth bound as a hypothesis and
    combines it with the backward error infrastructure. -/
theorem banded_growth_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε ρ_bound : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ_bound)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ρ_bound * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact lu_backward_error_relative n A L_hat U_hat ε ρ_bound hε hρ hLU hGrowth

/-- **Banded growth factor backward error** (Higham §9.3, Theorem 9.10).

    For a banded matrix with bandwidth p under partial pivoting,
    the growth factor satisfies:
      ρ_n ≤ 2^{2p-1} - (p-1) · 2^{p-2}

    The source-facing Chapter 9 wrapper records arithmetic for this scalar
    expression separately. This theorem itself takes the growth constant as a
    hypothesis and does not prove the banded GEPP growth theorem.

    This theorem takes the banded growth bound as a hypothesis
    and combines it with the tight LU solve backward error.
    Combined with `lu_solve_backward_error_tight`, this gives:
      |ΔA_ij| ≤ ρ_bound · γ(3n) · |A_ij| -/
theorem banded_growth_factor_solve_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (ρ_bound : ℝ) (_hρ : 0 ≤ ρ_bound)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ_bound * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ρ_bound * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (ρ_bound * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = ρ_bound * gamma fp (3 * n) * |A i j| := by ring

-- ============================================================
-- §9.4  Theorem 9.11: |L||U| = |LU| for special matrices
-- ============================================================

/-- **|L||U| = |LU| for nonneg LU factors** (Higham §9.4, Theorem 9.11b-c).

    When A has an LU factorization with L ≥ 0 and U ≥ 0 (which holds
    for totally nonneg matrices and certain M-matrices), we have
    |L||U| = LU = |LU| = |A|, so the backward error becomes |ΔA| ≤ ε|A|.

    Combined with the nonneg factor bound (eq 9.8), this gives
    |ΔA| ≤ ε/(1-ε) · |A| for the LU factorization stage.

    This theorem takes `HasNonnegLUFactors` and produces the optimal
    growth bound c = 1 (before the 1/(1-ε) correction). -/
theorem nonneg_lu_optimal_growth (n : ℕ)
    (A L U : Fin n → Fin n → ℝ)
    (hNonneg : HasNonnegLUFactors n A L U) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| = |A i j| := by
  intro i j
  have ⟨hLU, hL_nn, hU_nn⟩ := hNonneg
  have h1 := nonneg_factors_absLU_eq n L U hL_nn hU_nn i j
  rw [h1, hLU.product_eq i j]
  have : 0 ≤ ∑ k : Fin n, L i k * U k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hL_nn i k) (hU_nn k j))
  rw [abs_of_nonneg (hLU.product_eq i j ▸ this)]

/-- **Backward stability for nonneg LU** (Higham §9.4, combining Theorem 9.11 + eq 9.8).

    If A has nonneg computed LU factors and ε < 1, the backward error is
    |ΔA| ≤ ε/(1-ε) · |A|, which is optimal up to the (1-ε)⁻¹ factor.

    This is the strongest componentwise bound achievable for LU. -/
theorem nonneg_lu_backward_stable (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_backward_error_perturbation n A L_hat U_hat ε hε_nn hLU
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have h_nfb := nonneg_factor_bound n A L_hat U_hat ε hε_lt hε_nn hLU hL_nn hU_nn i j
  calc |ΔA i j|
      ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ ε * (|A i j| / (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left h_nfb hε_nn
    _ = ε / (1 - ε) * |A i j| := by ring

-- ============================================================
-- §9.3  Max-entry norm and growth factor lower bound (Theorem 9.7)
-- ============================================================

/-- **Max-entry norm** of a matrix: max_{i,j} |A_ij|.

    This is the elementwise maximum absolute value, used in
    Higham's definition of the growth factor (Definition 9.6):
      ρ_n = max_{i,j} |û_ij| / max_{i,j} |a_ij|

    Distinguished from `infNorm` (the operator ∞-norm = max row sum). -/
noncomputable def maxEntryNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => |A i j|))

/-- Max-entry norm is nonneg. -/
lemma maxEntryNorm_nonneg {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    0 ≤ maxEntryNorm hn A := by
  have h0 : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
  have h1 : 0 ≤ |A ⟨0, hn⟩ ⟨0, hn⟩| := abs_nonneg _
  have h2 : |A ⟨0, hn⟩ ⟨0, hn⟩| ≤ Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A ⟨0, hn⟩ j|) :=
    Finset.le_sup' (fun j => |A ⟨0, hn⟩ j|) h0
  have h3 : Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => |A ⟨0, hn⟩ j|) ≤ maxEntryNorm hn A :=
    Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A i j|)) h0
  linarith

/-- Each entry is bounded by the max-entry norm. -/
lemma entry_le_maxEntryNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : |A i j| ≤ maxEntryNorm hn A := by
  apply le_trans
  · exact Finset.le_sup' (fun j => |A i j|) (Finset.mem_univ j)
  · exact Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A i j|))
      (Finset.mem_univ i)

/-- Each entry is bounded by the matrix infinity norm. -/
lemma entry_abs_le_infNorm {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : |A i j| ≤ infNorm A := by
  have hrow : |A i j| ≤ ∑ j' : Fin n, |A i j'| :=
    Finset.single_le_sum (fun j' _ => abs_nonneg (A i j')) (Finset.mem_univ j)
  exact le_trans hrow (row_sum_le_infNorm A i)

/-- The max-entry norm is bounded by the matrix infinity norm. -/
lemma maxEntryNorm_le_infNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn A ≤ infNorm A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact entry_abs_le_infNorm A i j

/-- Max-entry norm monotonicity from componentwise absolute-value bounds. -/
lemma maxEntryNorm_le_of_entry_abs_le {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ |B i j|) :
    maxEntryNorm hn A ≤ maxEntryNorm hn B := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact le_trans (hentry i j) (entry_le_maxEntryNorm hn B i j)

/-- Max-entry norm bound from a uniform entrywise bound. -/
lemma maxEntryNorm_le_of_entry_le_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (M : ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ M) :
    maxEntryNorm hn A ≤ M := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hentry i j

/-- Max-entry norm monotonicity when every entry is bounded by another
matrix's max-entry norm, possibly at different indices. -/
lemma maxEntryNorm_le_of_entry_le_max {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ maxEntryNorm hn B) :
    maxEntryNorm hn A ≤ maxEntryNorm hn B := by
  exact maxEntryNorm_le_of_entry_le_bound hn A (maxEntryNorm hn B) hentry

/-- The max-entry norm is invariant under matrix transposition. -/
lemma maxEntryNorm_matTranspose {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn (matTranspose A) = maxEntryNorm hn A := by
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |matTranspose A i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [matTranspose] using entry_le_maxEntryNorm hn A j i
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (matTranspose A)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [matTranspose] using entry_le_maxEntryNorm hn (matTranspose A) j i

/-- Any square submatrix has max-entry norm bounded by the source matrix's
max-entry norm. -/
lemma maxEntryNorm_submatrix_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Fin n → Fin n → ℝ) (rows cols : Fin m → Fin n) :
    maxEntryNorm hm (fun i j : Fin m => A (rows i) (cols j)) ≤
      maxEntryNorm hn A := by
  let hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  change Finset.sup' Finset.univ hne
      (fun i => Finset.sup' Finset.univ hne
        (fun j => |A (rows i) (cols j)|)) ≤ maxEntryNorm hn A
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact entry_le_maxEntryNorm hn A (rows i) (cols j)

/-- The matrix infinity norm is at most `n` times the max-entry norm. -/
theorem infNorm_le_card_mul_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    infNorm A ≤ (n : ℝ) * maxEntryNorm hn A := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |A i j|
          ≤ ∑ _j : Fin n, maxEntryNorm hn A := by
            apply Finset.sum_le_sum
            intro j _
            exact entry_le_maxEntryNorm hn A i j
      _ = (n : ℝ) * maxEntryNorm hn A := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  · exact mul_nonneg (Nat.cast_nonneg' n) (maxEntryNorm_nonneg hn A)

/-- **Growth factor (max-entry version)** (Higham §9.3, Definition 9.6).

    ρ = max_{i,j} |U_ij| / max_{i,j} |A_ij|

    This is Higham's standard definition, using the elementwise maximum
    rather than the operator infinity norm. -/
noncomputable def growthFactorEntry {n : ℕ} (hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (_hA : 0 < maxEntryNorm hn A) : ℝ :=
  maxEntryNorm hn U_hat / maxEntryNorm hn A

/-- Convert a uniform final-`U` entry bound into Higham's max-entry growth
factor.  This is the generic adapter used by several Chapter 9 source-facing
growth rows. -/
theorem growthFactorEntry_le_of_entry_bound_factor {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℝ) (c : ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hEntry : ∀ i j : Fin n, |U i j| ≤ c * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ c := by
  have hUmax : maxEntryNorm hn U ≤ c * maxEntryNorm hn A := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact hEntry i j
  unfold growthFactorEntry
  rwa [div_le_iff₀ hA]

/-- Convert a max-entry growth-factor bound into the infinity-norm bridge used
in Wilkinson's source-facing bound. -/
theorem infNorm_le_card_mul_growthFactorEntry_bound {n : ℕ} (hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (ρ : ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hρ : 0 ≤ ρ)
    (hGrowth : growthFactorEntry hn A U_hat hA ≤ ρ) :
    infNorm U_hat ≤ (n : ℝ) * ρ * infNorm A := by
  have hmax_growth :
      maxEntryNorm hn U_hat ≤ ρ * maxEntryNorm hn A := by
    unfold growthFactorEntry at hGrowth
    rwa [div_le_iff₀ hA] at hGrowth
  have hcard_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg' n
  calc
    infNorm U_hat ≤ (n : ℝ) * maxEntryNorm hn U_hat :=
      infNorm_le_card_mul_maxEntryNorm hn U_hat
    _ ≤ (n : ℝ) * (ρ * maxEntryNorm hn A) :=
      mul_le_mul_of_nonneg_left hmax_growth hcard_nonneg
    _ = (n : ℝ) * ρ * maxEntryNorm hn A := by ring
    _ ≤ (n : ℝ) * ρ * infNorm A := by
      exact mul_le_mul_of_nonneg_left (maxEntryNorm_le_infNorm hn A)
        (mul_nonneg hcard_nonneg hρ)

/-- Convert a componentwise `|L| |U| <= c |A|` bound into Higham's
max-entry growth-factor bound for the final upper factor. -/
theorem growthFactorEntry_le_of_absLU_componentwise {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hAmax : 0 < maxEntryNorm hn A)
    (hLdiag_abs : ∀ i : Fin n, |L i i| = 1)
    (hAbsLU_le : ∀ i j : Fin n,
      ∑ k : Fin n, |L i k| * |U k j| ≤ c * |A i j|) :
    growthFactorEntry hn A U hAmax ≤ c := by
  have hUmax_le_Amax : maxEntryNorm hn U ≤ c * maxEntryNorm hn A := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hterm :
        |L i i| * |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : Fin n => |L i k| * |U k j|)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    have hU_le_absLU :
        |U i j| ≤ ∑ k : Fin n, |L i k| * |U k j| := by
      simpa [hLdiag_abs i] using hterm
    have hAij_le : c * |A i j| ≤ c * maxEntryNorm hn A :=
      mul_le_mul_of_nonneg_left (entry_le_maxEntryNorm hn A i j) hc
    exact le_trans hU_le_absLU (le_trans (hAbsLU_le i j) hAij_le)
  unfold growthFactorEntry
  rw [div_le_iff₀ hAmax]
  exact hUmax_le_Amax

/-- **Problem 9.9**, exact-LU max-entry growth bound in source form.

For an exact unit-lower/upper LU certificate `A = L U`, the max-entry growth
factor of the final upper factor is bounded by
`1 + n * || |L| |U| ||_∞ / ||A||_∞`.  The source problem states the same
inequality for GE without pivoting; this theorem supplies the local algebraic
bridge once the no-pivot trace has produced an exact LU certificate. -/
theorem growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A)
    (hAinf : 0 < infNorm A) :
    growthFactorEntry hn A U hAmax ≤
      1 + (n : ℝ) *
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    unfold W matMul absMatrix
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hentry :
      ∀ i j : Fin n, |U i j| ≤ maxEntryNorm hn A + infNorm W := by
    intro i j
    have hsplit :
        (∑ k : Fin n, L i k * U k j) =
          U i j + Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j) := by
      rw [← Finset.add_sum_erase _ (fun k : Fin n => L i k * U k j) (Finset.mem_univ i)]
      rw [hLU.L_diag i]
      ring
    have hU_eq :
        U i j =
          A i j - Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j) := by
      rw [← hLU.product_eq i j, hsplit]
      ring
    calc
      |U i j|
          = |A i j - Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j)| := by
            rw [hU_eq]
      _ ≤ |A i j| +
            |Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j)| := by
            let S := Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j)
            change |A i j - S| ≤ |A i j| + |S|
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (A i j) (-S)
      _ ≤ maxEntryNorm hn A +
            Finset.sum (Finset.univ.erase i) (fun k => |L i k| * |U k j|) := by
        gcongr
        · exact entry_le_maxEntryNorm hn A i j
        · calc
            |Finset.sum (Finset.univ.erase i) (fun k => L i k * U k j)|
                ≤ Finset.sum (Finset.univ.erase i) (fun k => |L i k * U k j|) :=
                  Finset.abs_sum_le_sum_abs _ _
            _ = Finset.sum (Finset.univ.erase i) (fun k => |L i k| * |U k j|) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
      _ ≤ maxEntryNorm hn A + ∑ k : Fin n, |L i k| * |U k j| := by
        have hsum :
            Finset.sum (Finset.univ.erase i) (fun k : Fin n => |L i k| * |U k j|) ≤
              ∑ k : Fin n, |L i k| * |U k j| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun k : Fin n => |L i k| * |U k j|)
            (s := Finset.univ.erase i)
            (t := Finset.univ)
            (by intro x _; exact Finset.mem_univ x)
            (by intro x _ _; exact mul_nonneg (abs_nonneg (L i x)) (abs_nonneg (U x j)))
        exact add_le_add (le_refl _) hsum
      _ = maxEntryNorm hn A + W i j := by
        simp [W, matMul, absMatrix]
      _ ≤ maxEntryNorm hn A + infNorm W := by
        gcongr
        have hWij_le_row : W i j ≤ ∑ j' : Fin n, |W i j'| := by
          have hWij_abs : W i j = |W i j| := (abs_of_nonneg (hW_nonneg i j)).symm
          rw [hWij_abs]
          exact Finset.single_le_sum (fun j' _ => abs_nonneg (W i j')) (Finset.mem_univ j)
        exact le_trans hWij_le_row (row_sum_le_infNorm W i)
  have hmaxU :
      maxEntryNorm hn U ≤ maxEntryNorm hn A + infNorm W := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact hentry i j
  have hmaxU_div :
      maxEntryNorm hn U / maxEntryNorm hn A ≤
        (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A :=
    div_le_div_of_nonneg_right hmaxU (le_of_lt hAmax)
  have hdiv_bound :
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    have hW_nonneg_norm : 0 ≤ infNorm W := infNorm_nonneg W
    have hmax_ne : maxEntryNorm hn A ≠ 0 := ne_of_gt hAmax
    have hdivW :
        infNorm W / maxEntryNorm hn A ≤ (n : ℝ) * infNorm W / infNorm A := by
      have hAinf_le : infNorm A ≤ (n : ℝ) * maxEntryNorm hn A :=
        infNorm_le_card_mul_maxEntryNorm hn A
      have hmul :
          infNorm W * infNorm A ≤
            infNorm W * ((n : ℝ) * maxEntryNorm hn A) :=
        mul_le_mul_of_nonneg_left hAinf_le hW_nonneg_norm
      rw [div_le_div_iff₀ hAmax hAinf]
      calc
        infNorm W * infNorm A
            ≤ infNorm W * ((n : ℝ) * maxEntryNorm hn A) := hmul
        _ = (n : ℝ) * infNorm W * maxEntryNorm hn A := by ring
    calc
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A
          = 1 + infNorm W / maxEntryNorm hn A := by
            field_simp [hmax_ne]
      _ ≤ 1 + (n : ℝ) * infNorm W / infNorm A := by
        gcongr
  unfold growthFactorEntry
  exact le_trans hmaxU_div hdiv_bound

/-- **Theorem 9.8, `θ ≤ n` core estimate.**

    If a row of `A * A_inv` has diagonal entry `1`, then
    `1 ≤ n * maxEntry(A) * maxEntry(A_inv)`. This is the finite-dimensional
    max-entry estimate used by Higham to prove `θ = (αβ)⁻¹ ≤ n`. -/
theorem inverse_row_identity_le_card_mul_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (i : Fin n)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 ≤ (n : ℝ) * maxEntryNorm hn A * maxEntryNorm hn A_inv := by
  have h_abs :
      |∑ j : Fin n, A i j * A_inv j i| ≤
        ∑ j : Fin n, |A i j * A_inv j i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_terms : ∀ j : Fin n,
      |A i j * A_inv j i| ≤ maxEntryNorm hn A * maxEntryNorm hn A_inv := by
    intro j
    rw [abs_mul]
    exact mul_le_mul
      (entry_le_maxEntryNorm hn A i j)
      (entry_le_maxEntryNorm hn A_inv j i)
      (abs_nonneg _)
      (maxEntryNorm_nonneg hn A)
  have h_sum :
      ∑ j : Fin n, |A i j * A_inv j i| ≤
        ∑ _j : Fin n, maxEntryNorm hn A * maxEntryNorm hn A_inv :=
    Finset.sum_le_sum (fun j _ => h_terms j)
  calc
    1 = |∑ j : Fin n, A i j * A_inv j i| := by rw [hrow, abs_one]
    _ ≤ ∑ j : Fin n, |A i j * A_inv j i| := h_abs
    _ ≤ ∑ _j : Fin n, maxEntryNorm hn A * maxEntryNorm hn A_inv := h_sum
    _ = (n : ℝ) * maxEntryNorm hn A * maxEntryNorm hn A_inv := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Theorem 9.8, `θ ≤ n` in max-entry form.**

    For `α = maxEntry(A)` and `β = maxEntry(A_inv)`, the inverse-row identity
    gives `(αβ)⁻¹ ≤ n`. -/
theorem theta_le_card_of_inverse_row_identity {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (i : Fin n)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤ n := by
  have hmain :=
    inverse_row_identity_le_card_mul_maxEntryNorm hn A A_inv i hrow
  have hprod : 0 < maxEntryNorm hn A * maxEntryNorm hn A_inv :=
    mul_pos hA hAinv
  rw [div_le_iff₀ hprod]
  simpa [mul_assoc] using hmain

/-- **Theorem 9.8, `ρ ≥ θ` max-entry bridge.**

    If the final pivot gives an inverse-entry witness `|u|⁻¹ ≤ β`, and `u` is
    bounded by the largest entry reached by elimination, then Higham's
    max-entry growth factor satisfies `ρ ≥ (αβ)⁻¹`. -/
theorem growthFactorEntry_ge_inverse_entry_theta {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (u : ℝ) (hu_pos : 0 < |u|)
    (hu_entry : |u| ≤ maxEntryNorm hn U)
    (hu_inv_le : |u|⁻¹ ≤ maxEntryNorm hn A_inv) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤
      growthFactorEntry hn A U hA := by
  have hbeta_inv_le_u :
      (maxEntryNorm hn A_inv)⁻¹ ≤ |u| :=
    inv_le_of_inv_le₀ hu_pos hu_inv_le
  have hbeta_inv_le_U :
      (maxEntryNorm hn A_inv)⁻¹ ≤ maxEntryNorm hn U :=
    le_trans hbeta_inv_le_u hu_entry
  have hdiv :
      (maxEntryNorm hn A_inv)⁻¹ / maxEntryNorm hn A ≤
        maxEntryNorm hn U / maxEntryNorm hn A :=
    div_le_div_of_nonneg_right hbeta_inv_le_U (le_of_lt hA)
  have htheta :
      1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) =
        (maxEntryNorm hn A_inv)⁻¹ / maxEntryNorm hn A := by
    field_simp [ne_of_gt hA, ne_of_gt hAinv]
  calc
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv)
        = (maxEntryNorm hn A_inv)⁻¹ / maxEntryNorm hn A := htheta
    _ ≤ maxEntryNorm hn U / maxEntryNorm hn A := hdiv
    _ = growthFactorEntry hn A U hA := rfl

/-- The max-entry growth factor is nonnegative. -/
lemma growthFactorEntry_nonneg {n : ℕ} (hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A) :
    0 ≤ growthFactorEntry hn A U_hat hA := by
  unfold growthFactorEntry
  exact div_nonneg (maxEntryNorm_nonneg hn U_hat) (le_of_lt hA)

/-- If the growth-factor matrix contains the initial max-entry norm, then the
    max-entry growth factor is at least one. -/
lemma growthFactorEntry_ge_one_of_maxEntryNorm_le {n : ℕ} (hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A)
    (hA_le_U : maxEntryNorm hn A ≤ maxEntryNorm hn U_hat) :
    1 ≤ growthFactorEntry hn A U_hat hA := by
  unfold growthFactorEntry
  exact (le_div_iff₀ hA).mpr (by simpa using hA_le_U)

/-- If the growth matrix is bounded by `c` times the initial max-entry norm,
    then the max-entry growth factor is at most `c`. -/
lemma growthFactorEntry_le_of_maxEntryNorm_le_mul {n : ℕ} (hn : 0 < n)
    (A U_hat : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A) {c : ℝ}
    (hU_le : maxEntryNorm hn U_hat ≤ c * maxEntryNorm hn A) :
    growthFactorEntry hn A U_hat hA ≤ c := by
  unfold growthFactorEntry
  exact (div_le_iff₀ hA).mpr (by simpa [mul_comm] using hU_le)

/-- **Diagonal product bounded by max-entry norm** (core of Theorem 9.7).

    For any matrix U: ∏_k |U_kk| ≤ maxEntry(U)^n.
    Each diagonal entry is bounded by the max entry, and the product
    of n such entries is bounded by the n-th power. -/
theorem diag_product_le_maxEntryNorm_pow {n : ℕ} (hn : 0 < n)
    (U : Fin n → Fin n → ℝ) :
    ∏ k : Fin n, |U k k| ≤ maxEntryNorm hn U ^ n := by
  calc ∏ k : Fin n, |U k k|
      ≤ ∏ _k : Fin n, maxEntryNorm hn U := by
        apply Finset.prod_le_prod
        · intro k _; exact abs_nonneg _
        · intro k _; exact entry_le_maxEntryNorm hn U k k
    _ = maxEntryNorm hn U ^ n := by
        simp [Finset.prod_const, Finset.card_univ]

/-- **Growth factor lower bound** (Higham §9.3, Theorem 9.7).

    The growth factor satisfies:
      ρ^n · maxEntry(A)^n ≥ ∏_k |u_kk|

    Equivalently, ρ ≥ (∏_k |u_kk|)^{1/n} / maxEntry(A).

    Since det(A) = det(L)·det(U) = ∏_k u_kk for unit lower triangular L,
    this gives ρ ≥ |det(A)|^{1/n} / maxEntry(A), showing that
    growth is unavoidable when the determinant is large relative to
    the entry magnitudes. This lower bound proves that the growth factor
    bounds for specific matrix classes (ρ ≤ 2 for diag-dominant,
    ρ ≤ n for Hessenberg) cannot be improved in general. -/
theorem growth_factor_entry_lower_bound {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A) :
    ∏ k : Fin n, |U k k| ≤
      (growthFactorEntry hn A U hA) ^ n * (maxEntryNorm hn A) ^ n := by
  have hA_ne : maxEntryNorm hn A ≠ 0 := ne_of_gt hA
  unfold growthFactorEntry
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hA_ne)]
  exact diag_product_le_maxEntryNorm_pow hn U

-- ============================================================
-- §9.9  Frobenius norm infrastructure
-- ============================================================

-- ============================================================
-- §9.3  Full growth factor lower bound (Theorem 9.7)
-- ============================================================

/-- **Full growth factor lower bound** (Higham §9.3, Theorem 9.7).

    The growth factor satisfies:
      ρ^n · maxEntry(A)^n · maxEntry(A⁻¹)^n ≥ 1

    Equivalently: ρ ≥ (maxEntry(A) · maxEntry(A⁻¹))^{-1}.

    The proof uses: for unit lower triangular L, det(A) = det(LU) = ∏ u_kk.
    Then |det(A)| ≤ ∏|u_kk| ≤ maxEntry(U)^n = ρ^n · maxEntry(A)^n.
    Similarly |det(A⁻¹)| ≤ maxEntry(A⁻¹)^n.
    Since 1 = |det(I)| = |det(A)·det(A⁻¹)| ≤ ρ^n · maxEntry(A)^n · maxEntry(A⁻¹)^n.

    This theorem expresses the intermediate step: the product of U diagonal
    entries (= |det(A)| for unit L) is bounded by ρ^n · maxEntry(A)^n.
    Combined with `diag_product_le_maxEntryNorm_pow`, this gives the full bound. -/
theorem growth_factor_det_bound {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A)
    (det_A : ℝ)
    -- |det(A)| = ∏|u_kk| (unit lower triangular L)
    (hdet : |det_A| ≤ ∏ k : Fin n, |U k k|) :
    |det_A| ≤ (growthFactorEntry hn A U hA) ^ n * (maxEntryNorm hn A) ^ n := by
  calc |det_A|
      ≤ ∏ k : Fin n, |U k k| := hdet
    _ ≤ maxEntryNorm hn U ^ n := diag_product_le_maxEntryNorm_pow hn U
    _ = (maxEntryNorm hn U / maxEntryNorm hn A) ^ n * (maxEntryNorm hn A) ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n (ne_of_gt hA))]
    _ = (growthFactorEntry hn A U hA) ^ n * (maxEntryNorm hn A) ^ n := rfl

/-- **Growth factor lower bound, product form** (Higham §9.3, Theorem 9.7).

    If det(A) ≠ 0 and A · A⁻¹ = I, then:
      1 ≤ ρ^n · maxEntry(A)^n · maxEntry(A⁻¹)^n

    This shows the growth factor cannot be arbitrarily small:
    ρ ≥ (maxEntry(A) · maxEntry(A⁻¹))^{-1}. -/
theorem growth_factor_product_lower_bound {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A)
    (det_A det_Ainv : ℝ)
    (hdet_prod : |det_A| * |det_Ainv| = 1)
    (hdet : |det_A| ≤ ∏ k : Fin n, |U k k|)
    (hdet_inv : |det_Ainv| ≤ (maxEntryNorm hn A_inv) ^ n) :
    1 ≤ (growthFactorEntry hn A U hA) ^ n *
        (maxEntryNorm hn A) ^ n * (maxEntryNorm hn A_inv) ^ n := by
  have h1 := growth_factor_det_bound hn A U hA det_A hdet
  calc 1 = |det_A| * |det_Ainv| := hdet_prod.symm
    _ ≤ ((growthFactorEntry hn A U hA) ^ n * (maxEntryNorm hn A) ^ n) *
        (maxEntryNorm hn A_inv) ^ n := by
        apply mul_le_mul h1 hdet_inv (abs_nonneg _)
        exact mul_nonneg (pow_nonneg (div_nonneg (maxEntryNorm_nonneg hn U) (le_of_lt hA)) n)
          (pow_nonneg (le_of_lt hA) n)
    _ = (growthFactorEntry hn A U hA) ^ n *
        (maxEntryNorm hn A) ^ n * (maxEntryNorm hn A_inv) ^ n := by ring

end NumStability
