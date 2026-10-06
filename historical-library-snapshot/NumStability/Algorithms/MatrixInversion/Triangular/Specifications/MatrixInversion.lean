import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms MatrixInversion Triangular Specifications MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Specification for Method 2 triangular inversion**.

    Method 2 computes columns of X̂ ≈ L⁻¹ in reverse order j = n, n−1, …, 1.
    For each j:
      x̂ⱼⱼ = lⱼⱼ⁻¹(1 + δ),  |δ| ≤ u
      x̂(j+1:n, j) = x̂(j+1:n, j+1:n) · L(j+1:n, j)   (mat-vec multiply)
      x̂(j+1:n, j) = −x̂ⱼⱼ · x̂(j+1:n, j)              (scalar multiply)

    This is an abstract spec capturing the key error properties. -/
structure Method2Spec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- Diagonal entries: x̂ⱼⱼ = fl(1/lⱼⱼ), so x̂ⱼⱼlⱼⱼ = 1 + δ with |δ| ≤ u. -/
  diag_err : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
    X_hat j j * L j j = 1 + δ
  /-- Off-diagonal (below j): computed via mat-vec + scalar multiply with
      rounding errors bounded by Δ-notation. -/
  offdiag_err : ∀ j : Fin n, ∀ i : Fin n, i.val > j.val →
    ∃ Δ_mv : Fin n → ℝ,
      (∀ k : Fin n, |Δ_mv k| ≤ gamma fp n * |X_hat i k| * |L k j|) ∧
      X_hat i j = -X_hat j j * (∑ k : Fin n, X_hat i k * L k j) +
        Δ_mv j
  /-- Upper triangle is zero (since L is lower triangular, L⁻¹ is too). -/
  upper_zero : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0

/-- Higham, 2nd ed., Chapter 14, Section 14.2.1, Method 2:
    source-facing kernel certificate for the reverse-column strict-tail update.

    This packages the existing Method 2 diagonal/shape/error specification
    together with the exact stored below-diagonal update
    `fl_mul (-X_hat j j) (fl_dotProduct strictTail Lcol)`.  It is not yet the
    full loop proof; the remaining source obligation is to show the concrete
    reverse-column implementation produces this certificate. -/
structure Method2StrictTailKernelSpec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- Existing Method 2 diagonal, off-diagonal, and triangular-shape contract. -/
  method2 : Method2Spec fp n L X_hat
  /-- Below-diagonal entries are stored by the rounded strict-tail dot/scalar
      kernel described in the source Method 2 recurrence. -/
  strict_tail_dot_scalar : ∀ j row : Fin n, row.val > j.val →
    X_hat row j =
      fp.fl_mul (-X_hat j j)
        (fl_dotProduct fp n
          (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
          (fun k : Fin n => L k j))

/-- **Specification for block triangular inversion (Method 1B)**.

    Method 1B computes X̂ ≈ L⁻¹ in block form: for j = 1:N,
    diagonal blocks Xⱼⱼ = Lⱼⱼ⁻¹ by Method 1, then off-diagonal
    blocks by block forward substitution.

    The block indexing details are intentionally abstracted away; the reusable
    numerical content is the per-column backward-error contract produced by the
    diagonal block inversions and block forward substitutions. -/
structure BlockMethod1BSpec (fp : FPModel) (n N : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- The declared number of blocks is compatible with the matrix dimension. -/
  block_count_le_dim : N ≤ n
  /-- The computed inverse has the expected lower-triangular shape. -/
  lower_triangular_inverse : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0
  /-- Each computed column satisfies the backward-error contract obtained from
      the Method 1 diagonal block solve and the block forward substitutions. -/
  column_backward_error : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
    (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
    ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
      if i = j then 1 else 0

end NumStability
