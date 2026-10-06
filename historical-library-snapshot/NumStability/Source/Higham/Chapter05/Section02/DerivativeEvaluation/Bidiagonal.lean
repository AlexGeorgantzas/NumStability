import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter05 Section02 DerivativeEvaluation Bidiagonal

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham Chapter 5, equation (5.5): the unit upper-bidiagonal matrix
`U_n(alpha)` with diagonal entries `1` and superdiagonal entries `-alpha`.
For coefficient vectors in ascending order, the exact synthetic-division
coefficients satisfy `U_n(alpha) q = a`. -/
noncomputable def highamBidiagonalU (alpha : ℝ) (n : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = i.val then 1
    else if j.val = i.val + 1 then -alpha
    else 0

theorem highamBidiagonalU_diag
    (alpha : ℝ) (n : ℕ) (i : Fin n) :
    highamBidiagonalU alpha n i i = 1 := by
  simp [highamBidiagonalU]

theorem highamBidiagonalU_superdiag
    (alpha : ℝ) (n : ℕ) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    highamBidiagonalU alpha n i j = -alpha := by
  simp [highamBidiagonalU, hij]

theorem highamBidiagonalU_zero_of_not_diag_not_superdiag
    (alpha : ℝ) (n : ℕ) (i j : Fin n)
    (hdiag : j.val ≠ i.val) (hsuper : j.val ≠ i.val + 1) :
    highamBidiagonalU alpha n i j = 0 := by
  simp [highamBidiagonalU, hdiag, hsuper]

/-- Source-shaped componentwise majorant in (5.5):
`epsilon * |U^{-1}| |U| |qhat|`. -/
noncomputable def highamBidiagonalForwardErrorMajorant
    (alpha : ℝ) (n : ℕ) (Uinv : Fin n → Fin n → ℝ)
    (epsilon : ℝ) (qhat : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    epsilon *
      ∑ j : Fin n,
        |Uinv i j| *
          (∑ k : Fin n,
            |highamBidiagonalU alpha n j k| * |qhat k|)

/-- Higham (5.5), exact finite matrix bridge.  If `q` solves the exact
bidiagonal synthetic-division system `U q = a`, while `qhat` solves a
componentwise perturbed system `(U + DeltaU) qhat = a` with
`|DeltaU| <= epsilon |U|`, then the componentwise error is bounded by the
source matrix expression `epsilon |U^{-1}| |U| |qhat|`.

This is the exact version of the displayed first-order matrix form; replacing
`|qhat|` by `|q|` is the separate first-order/O(u^2) simplification tracked
under (5.7). -/
theorem highamBidiagonal_forward_error_from_backward
    (alpha : ℝ) (n : ℕ)
    (Uinv : Fin n → Fin n → ℝ)
    (q qhat a : Fin n → ℝ)
    (DeltaU : Fin n → Fin n → ℝ)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hInv : IsLeftInverse n (highamBidiagonalU alpha n) Uinv)
    (hUq :
      ∀ i : Fin n,
        ∑ j : Fin n, highamBidiagonalU alpha n i j * q j = a i)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (highamBidiagonalU alpha n i j + DeltaU i j) * qhat j =
            a i)
    (hDelta :
      ∀ i j : Fin n,
        |DeltaU i j| ≤ epsilon * |highamBidiagonalU alpha n i j|) :
    ∀ i : Fin n,
      |q i - qhat i| ≤
        highamBidiagonalForwardErrorMajorant alpha n Uinv epsilon qhat i := by
  intro i
  simpa [highamBidiagonalForwardErrorMajorant] using
    forward_error_from_backward_componentwise n
      (highamBidiagonalU alpha n) Uinv q qhat a DeltaU epsilon
      hepsilon hInv hUq hPerturbed hDelta i

end NumStability
