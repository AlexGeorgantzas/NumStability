import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite ErrorAnalysis BlockLDLT

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Block LDL^T factorization** (Higham Chapter 11).

    For a symmetric matrix A, the diagonal pivoting method computes:
      P A P^T = L D L^T

    where P is a permutation, L is unit lower triangular, and D is
    block diagonal with 1×1 or 2×2 diagonal blocks.

    The 2×2 blocks arise when a 1×1 pivot would be too small
    (potentially causing instability). Each 2×2 block is nonsingular. -/
structure BlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular: diagonal entries are 1. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular: entries above diagonal are 0. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is block diagonal with 1×1 or 2×2 blocks. -/
  D_block_diag : IsBlockDiag n D
  /-- P A P^T = L D L^T: the product recovers the permuted matrix. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Aasen factorization** source specification:
`P A P^T = L T L^T`, with `L` unit lower triangular, first column `e_1`,
and `T` symmetric tridiagonal. -/
structure AasenSpec (n : ℕ) (A L T : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- The first column of L is the first coordinate vector. -/
  L_first_col : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → L i j = 0
  /-- T is symmetric tridiagonal. -/
  T_tridiag : IsSymTridiagonal n T
  /-- P A P^T = L T L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- Skew-symmetric block LDL^T factorization source specification for
Chapter 11, equation (11.16). -/
structure SkewBlockLDLTSpec (n : ℕ) (A L D : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) : Prop where
  /-- The input is skew-symmetric. -/
  skew_A : IsSkewSymmetric n A
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L i i = 1
  /-- L is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  /-- D is skew block diagonal. -/
  D_skew_block_diag : IsSkewBlockDiag n D
  /-- P A P^T = L D L^T. -/
  product_eq : ∀ i j : Fin n,
    ∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * D k₁ k₂ * L j k₂ = A (σ i) (σ j)

/-- **Block LDL^T backward error** (Higham Chapter 11).

    The computed factors satisfy:
      |L̂ D̂ L̂^T − PAP^T| ≤ ε · |L̂| · |D̂| · |L̂^T|  componentwise -/
structure BlockLDLTBackwardError (n : ℕ) (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (ε : ℝ) : Prop where
  /-- σ is a permutation. -/
  perm : IsPermutation n σ
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- D̂ is block diagonal. -/
  D_block_diag : IsBlockDiag n D_hat
  /-- Componentwise backward error. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k₁ : Fin n, ∑ k₂ : Fin n, L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ -
      A (σ i) (σ j)| ≤
    ε * ∑ k₁ : Fin n, ∑ k₂ : Fin n, |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂|

/-- Pivot block size used by Chapter 11 algorithms. -/
inductive PivotSize where
  | one
  | two
  deriving DecidableEq, Repr

/-- Algorithm 11.1 source decision predicate for the first Bunch-Parlett
complete-pivoting step, expressed in terms of the printed scalar quantities
`mu0` and `mu1`. -/
def BunchParlettCompletePivotChoice (α μ0 μ1 : ℝ) (s : PivotSize) : Prop :=
  match s with
  | PivotSize.one => μ1 ≥ α * μ0
  | PivotSize.two => μ1 < α * μ0

/-- Branch labels for Algorithm 11.2. -/
inductive BunchKaufmanCase where
  | noAction
  | case1
  | case2
  | case3
  | case4
  deriving DecidableEq, Repr

/-- Algorithm 11.2 source decision predicate for the Bunch-Kaufman partial
pivoting tests at the first stage. -/
def BunchKaufmanPartialPivotCase
    (α a11 arr ω1 ωr : ℝ) (branch : BunchKaufmanCase) : Prop :=
  match branch with
  | BunchKaufmanCase.noAction => ω1 = 0
  | BunchKaufmanCase.case1 => ω1 ≠ 0 ∧ |a11| ≥ α * ω1
  | BunchKaufmanCase.case2 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr ≥ α * ω1 ^ 2
  | BunchKaufmanCase.case3 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| ≥ α * ωr
  | BunchKaufmanCase.case4 =>
      ω1 ≠ 0 ∧ |a11| < α * ω1 ∧ |a11| * ωr < α * ω1 ^ 2 ∧
        |arr| < α * ωr

/-- Algorithm 11.5 source predicate for a successful symmetric rook-pivot
first-stage decision.  The loop and search path are not modeled here; this
records the printed local tests that certify the returned pivot size. -/
def SymmetricRookFirstPivotChoice
    (α a11 arr ω1 ωr : ℝ) (s : PivotSize) : Prop :=
  (|a11| ≥ α * ω1 ∧ s = PivotSize.one) ∨
  (|arr| ≥ α * ωr ∧ s = PivotSize.one) ∨
  (ω1 = ωr ∧ s = PivotSize.two)

end NumStability
