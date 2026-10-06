import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite ErrorAnalysis Predicates

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- A symmetric tridiagonal matrix predicate, used by Aasen's method and by the
    symmetric-tridiagonal specialization of block LDL^T. -/
def IsSymTridiagonal (n : ℕ) (T : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, T i j = T j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0)

/-- A real skew-symmetric matrix predicate, `A^T = -A`. -/
def IsSkewSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j = -A j i

/-- A skew-symmetric matrix has zero diagonal. -/
theorem skewSymmetric_diag_zero (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hA : IsSkewSymmetric n A) :
    ∀ i : Fin n, A i i = 0 := by
  intro i
  have h := hA i i
  linarith

/-- **Block diagonal predicate** for the D factor in block LDL^T.

    D is block diagonal with blocks of size 1 or 2.
    Entries D_{ij} = 0 whenever i and j are not in the same block.

    We model this by requiring: for |i - j| > 1, D_{ij} = 0;
    and D is symmetric. The block structure means each 2×2 block
    [d_{k,k}  d_{k,k+1}; d_{k+1,k}  d_{k+1,k+1}] is nonsingular. -/
def IsBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, D i j = D j i) ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

/-- Skew block diagonal structure for Chapter 11, equation (11.16): diagonal
    blocks are zero `1x1` blocks or skew `2x2` blocks. -/
def IsSkewBlockDiag (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  IsSkewSymmetric n D ∧
  (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → D i j = 0)

end NumStability
