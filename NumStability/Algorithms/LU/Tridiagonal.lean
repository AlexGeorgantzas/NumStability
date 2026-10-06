-- Algorithms/LU/Tridiagonal.lean
--
-- Tridiagonal and banded matrix structures with specialized LU bounds
-- (Higham §9.5, Theorems 9.11–9.13).
--
-- Tridiagonal and banded systems are ubiquitous in numerical computing
-- (finite differences, spline interpolation, etc.). Their special structure
-- gives sharper backward error bounds than the general LU analysis:
--   - Banded: γ(bandwidth) instead of γ(n)
--   - Tridiag + diag dominant: |L̂||Û| ≤ 3|A|, giving |ΔA| ≤ 3ε|A|

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.5  Matrix structure predicates
-- ============================================================

/-- **Tridiagonal matrix** predicate.

    A matrix A is tridiagonal if A_ij = 0 whenever |i - j| > 1,
    i.e., entries more than one position from the diagonal are zero.

    Tridiagonal systems arise from finite difference discretizations,
    cubic spline interpolation, and many other applications. -/
def IsTridiagonal (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, (i.val + 1 < j.val ∨ j.val + 1 < i.val) → A i j = 0

/-- **Banded matrix** predicate (general bandwidth).

    A matrix A has lower bandwidth p and upper bandwidth q if
    A_ij = 0 whenever i > j + p or j > i + q.

    Special cases:
    - Diagonal: p = q = 0
    - Tridiagonal: p = q = 1
    - Upper triangular: p = 0, q = n-1
    - Lower triangular: p = n-1, q = 0

    For banded LU, the backward error uses γ(min(p,q)+1) instead of γ(n). -/
def IsBanded (n : ℕ) (p q : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, (i.val > j.val + p ∨ j.val > i.val + q) → A i j = 0

/-- Tridiagonal is the special case of banded with p = q = 1. -/
lemma isTridiagonal_iff_isBanded (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsTridiagonal n A ↔ IsBanded n 1 1 A := by
  constructor
  · intro h i j hij
    exact h i j (by omega)
  · intro h i j hij
    exact h i j (by omega)

/-- Tridiagonal matrices are banded with lower and upper bandwidth one. -/
lemma isBanded_one_one_of_isTridiagonal {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsTridiagonal n A) :
    IsBanded n 1 1 A :=
  (isTridiagonal_iff_isBanded n A).1 hA

/-- Banded matrices with lower and upper bandwidth one are tridiagonal. -/
lemma isTridiagonal_of_isBanded_one_one {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsBanded n 1 1 A) :
    IsTridiagonal n A :=
  (isTridiagonal_iff_isBanded n A).2 hA

/-- Widening the lower and upper bandwidth preserves bandedness. -/
lemma isBanded_mono {n p q p' q' : ℕ} {A : Fin n → Fin n → ℝ}
    (hp : p ≤ p') (hq : q ≤ q') (hA : IsBanded n p q A) :
    IsBanded n p' q' A := by
  intro i j hij
  exact hA i j (by
    rcases hij with hij | hij
    · left
      omega
    · right
      omega)

/-- A matrix with lower bandwidth `p` and upper bandwidth `q` is banded with a
common bandwidth `r` whenever both original bandwidths are at most `r`. -/
lemma isBanded_common_of_le {n p q r : ℕ} {A : Fin n → Fin n → ℝ}
    (hp : p ≤ r) (hq : q ≤ r) (hA : IsBanded n p q A) :
    IsBanded n r r A :=
  isBanded_mono hp hq hA

-- ============================================================
-- §9.5  Banded LU backward error
-- ============================================================

/-- **Banded LU backward error** (Higham §9.5).

    For a banded matrix with lower bandwidth p and upper bandwidth q,
    the LU backward error uses γ(min(p,q)+1) instead of γ(n):
      |L̂Û - A|_ij ≤ γ(min(p,q)+1) · (|L̂||Û|)_ij

    This is because each inner product in the factorization involves
    at most min(p,q)+1 nonzero terms, so fewer rounding errors accumulate.

    The theorem takes the `LUBackwardError` specification with the
    bandwidth-adapted γ as input. -/
theorem banded_lu_backward_error (fp : FPModel) (n p q : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (_hBanded : IsBanded n p q A)
    (hn : gammaValid fp (min p q + 1))
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp (min p q + 1))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (min p q + 1) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_perturbation n A L_hat U_hat
    (gamma fp (min p q + 1)) (gamma_nonneg fp hn) hLU

/-- **Banded LU backward error (correct)** (Higham §9.5, eq 9.13).

    For a banded matrix with lower bandwidth p and upper bandwidth q,
    each inner product in the factorization involves at most max(p,q)+1
    nonzero terms, giving the backward error bound:
      |L̂Û - A|_ij ≤ γ(max(p,q)+1) · (|L̂||Û|)_ij

    This corrects the conservative `min(p,q)+1` to the book's `max(p,q)+1`. -/
theorem banded_lu_backward_error_correct (fp : FPModel) (n p q : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (_hBanded : IsBanded n p q A)
    (hn : gammaValid fp (Nat.max p q + 1))
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp (Nat.max p q + 1))) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (Nat.max p q + 1) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_perturbation n A L_hat U_hat
    (gamma fp (Nat.max p q + 1)) (gamma_nonneg fp hn) hLU

/-- **Tridiagonal LU backward error** (Higham §9.5, specialization).

    For a tridiagonal matrix (bandwidth 1), γ(2) replaces γ(n):
      |L̂Û - A|_ij ≤ γ(2) · (|L̂||Û|)_ij

    This is much sharper than the general bound for large n. -/
theorem tridiag_lu_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (_hTridiag : IsTridiagonal n A)
    (hn : gammaValid fp 2)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp 2)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp 2 *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_perturbation n A L_hat U_hat
    (gamma fp 2) (gamma_nonneg fp hn) hLU

-- ============================================================
-- §9.5  Tridiagonal diag-dominant bounds (Theorem 9.12)
-- ============================================================

/-- **Tridiagonal diag-dominant LU backward error** (Higham §9.5, Theorem 9.12).

    For a diagonally dominant tridiagonal matrix, the computed LU factors
    satisfy |L̂||Û| ≤ 3|A| componentwise (Theorem 9.12). Combined with
    the LU backward error, this gives |ΔA| ≤ 3ε|A|.

    The growth bound c = 3 comes from the tridiagonal structure:
    each row of L̂ has at most 2 nonzero entries (diagonal = 1, one subdiag),
    each column of Û has at most 2 nonzero entries (diagonal + one superdiag).

    This theorem takes the structural bound as a hypothesis. -/
theorem tridiag_diagDom_lu_backward_error (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * 3 * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact lu_backward_error_relative n A L_hat U_hat ε 3 hε (by linarith) hLU hGrowth

/-- **Tridiagonal diag-dominant full solve stability** (Higham §9.5, Theorem 9.13).

    For a diagonally dominant tridiagonal system solved via LU + triangular solves,
    the total backward error satisfies:
      (A + ΔA)x̂ = b  with  |ΔA_ij| ≤ 3(3γ(n) + γ(n)²)|A_ij|

    This is the tridiagonal analogue of `diagDom_lu_solve_backward_stable`
    with growth bound 3 instead of 2. -/
theorem tridiag_diagDom_lu_solve_backward_stable (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * (3 * gamma fp n + gamma fp n ^ 2) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error fp n A L_hat U_hat b hL_diag hU_diag hLU hn
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  calc |ΔA i j|
      ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ (3 * gamma fp n + gamma fp n ^ 2) * (3 * |A i j|) := by
        apply mul_le_mul_of_nonneg_left (hGrowth i j)
        have hγ := gamma_nonneg fp hn
        nlinarith [sq_nonneg (gamma fp n)]
    _ = 3 * (3 * gamma fp n + gamma fp n ^ 2) * |A i j| := by ring

-- ============================================================
-- §9.5  Banded solve backward error
-- ============================================================

/-- **Banded matrix solve backward error** (Higham §9.5, general version).

    For a banded matrix with lower bandwidth p and upper bandwidth q,
    if the growth is bounded by c, the full solve backward error is:
      |ΔA_ij| ≤ c · (3γ(n) + γ(n)²) · |A_ij|

    This generalizes the tridiagonal and diag-dominant results. -/
theorem banded_lu_solve_backward_stable (fp : FPModel) (n : ℕ) (c : ℝ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (_hc : 0 ≤ c)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        c * (3 * gamma fp n + gamma fp n ^ 2) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error fp n A L_hat U_hat b hL_diag hU_diag hLU hn
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  calc |ΔA i j|
      ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ (3 * gamma fp n + gamma fp n ^ 2) * (c * |A i j|) := by
        apply mul_le_mul_of_nonneg_left (hGrowth i j)
        have hγ := gamma_nonneg fp hn
        nlinarith [sq_nonneg (gamma fp n)]
    _ = c * (3 * gamma fp n + gamma fp n ^ 2) * |A i j| := by ring

/-- **Tight tridiag diag-dominant solve stability** (Higham §9.5, Theorem 9.13).

    Absorbs 3γ(n) + γ(n)² into γ(3n):
      |ΔA_ij| ≤ 3 · γ(3n) · |A_ij| -/
theorem tridiag_diagDom_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (3 * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = 3 * gamma fp (3 * n) * |A i j| := by ring

/-- **Tight banded solve backward error** (Higham §9.5).

    Absorbs 3γ(n) + γ(n)² into γ(3n):
      |ΔA_ij| ≤ c · γ(3n) · |A_ij| -/
theorem banded_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ) (c : ℝ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (_hc : 0 ≤ c)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ c * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ3n := gamma_nonneg fp hn3
  calc |ΔA i j|
      ≤ gamma fp (3 * n) * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (c * |A i j|) :=
        mul_le_mul_of_nonneg_left (hGrowth i j) hγ3n
    _ = c * gamma fp (3 * n) * |A i j| := by ring

-- ============================================================
-- §9.5  Tridiagonal f(u) bound (eq 9.19)
-- ============================================================

/-- **Tridiagonal f(u) bound** (Higham §9.5, eq 9.19, expanded form).

    For tridiagonal diagonally dominant systems, the LU factorization uses γ(2)
    (bidiagonal inner products) and the triangular solves also use γ(2) (bidiagonal
    structure → 2 operations per row). Combined with |L̂||Û| ≤ 3|A|:

      |ΔA_ij| ≤ 3 · (3γ₂ + γ₂²) · |A_ij|

    This is the tridiagonal specialization of the solve backward error,
    using bandwidth 2 instead of dimension n throughout. -/
theorem tridiag_diagDom_fu_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2)
    -- LU factorization error with γ(2) (bidiagonal inner products)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    -- Forward sub error with γ(2) (bidiagonal L)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    -- Back sub error with γ(2) (bidiagonal U)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i)
    -- Growth bound from Theorem 9.12
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        3 * (3 * gamma fp 2 + gamma fp 2 ^ 2) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_bw n A L_hat U_hat y_hat x_hat
      (gamma fp 2) (gamma_nonneg fp h2)
      ΔA_LU hΔA_LU_bound hΔA_LU_eq b ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hγ2 := gamma_nonneg fp h2
  calc |ΔA i j|
      ≤ (3 * gamma fp 2 + gamma fp 2 ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ (3 * gamma fp 2 + gamma fp 2 ^ 2) * (3 * |A i j|) := by
        apply mul_le_mul_of_nonneg_left (hGrowth i j)
        nlinarith [sq_nonneg (gamma fp 2)]
    _ = 3 * (3 * gamma fp 2 + gamma fp 2 ^ 2) * |A i j| := by ring

/-- **Tridiagonal f(u) bound, tight** (Higham §9.5, eq 9.19, absorbed form).

    Absorbs 3γ(2) + γ(2)² into γ(6) using `three_gamma_plus_sq_le_gamma`:
      |ΔA_ij| ≤ 3 · γ(6) · |A_ij|

    This is the book's stated bound for tridiagonal diagonally dominant systems. -/
theorem tridiag_diagDom_fu_bound_tight (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (y_hat x_hat : Fin n → ℝ)
    (b : Fin n → ℝ)
    (fp : FPModel) (h2 : gammaValid fp 2) (h6 : gammaValid fp 6)
    (ΔA_LU : Fin n → Fin n → ℝ)
    (hΔA_LU_bound : ∀ i j, |ΔA_LU i j| ≤
      gamma fp 2 * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hΔA_LU_eq : ∀ i j,
      ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA_LU i j)
    (ΔL : Fin n → Fin n → ℝ)
    (hΔL_bound : ∀ i j, |ΔL i j| ≤ gamma fp 2 * |L_hat i j|)
    (hΔL_eq : ∀ i, ∑ j : Fin n, (L_hat i j + ΔL i j) * y_hat j = b i)
    (ΔU : Fin n → Fin n → ℝ)
    (hΔU_bound : ∀ i j, |ΔU i j| ≤ gamma fp 2 * |U_hat i j|)
    (hΔU_eq : ∀ i, ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y_hat i)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 3 * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 3 * gamma fp 6 * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    tridiag_diagDom_fu_bound n A L_hat U_hat y_hat x_hat b fp h2
      ΔA_LU hΔA_LU_bound hΔA_LU_eq ΔL hΔL_bound hΔL_eq ΔU hΔU_bound hΔU_eq hGrowth
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have h_absorb := three_gamma_plus_sq_le_gamma fp 2 (by rwa [show 3 * 2 = 6 from by omega])
  calc |ΔA i j|
      ≤ 3 * (3 * gamma fp 2 + gamma fp 2 ^ 2) * |A i j| := hΔA_bound i j
    _ ≤ 3 * gamma fp (3 * 2) * |A i j| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left h_absorb (by linarith)
    _ = 3 * gamma fp 6 * |A i j| := by norm_num

end NumStability
