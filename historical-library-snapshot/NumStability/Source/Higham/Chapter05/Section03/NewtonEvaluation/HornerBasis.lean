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
# Chapter05 Section03 NewtonEvaluation HornerBasis

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.8):
auxiliary accumulator for the Newton form
`sum_i c_i * prod_{j<i} (x - alpha_j)`.  The argument `basis` carries the
current prefix product. -/
noncomputable def newtonFormAux (x : ℝ) :
    List ℝ → List ℝ → ℝ → ℝ
  | [], _nodes, _basis => 0
  | c :: _cs, [], basis => c * basis
  | c :: cs, alpha :: nodes, basis =>
      c * basis + newtonFormAux x cs nodes (basis * (x - alpha))

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.8):
the Newton-form polynomial
`p(x) = sum_i c_i * prod_{j<i} (x - alpha_j)`.

The coefficient list is `[c_0, ..., c_n]`; the node list starts with
`[alpha_0, ...]`.  Extra nodes are ignored, as in the source formula where
`alpha_n` is interpolation data but not used in the product for `c_n`. -/
noncomputable def newtonForm (x : ℝ) (coeffs nodes : List ℝ) : ℝ :=
  newtonFormAux x coeffs nodes 1

/-- Nested Horner-like evaluation of the Newton-form polynomial:
`q_i = c_i + (x - alpha_i) q_{i+1}`. -/
noncomputable def newtonFormNested (x : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], _nodes => 0
  | c :: _cs, [] => c
  | c :: cs, alpha :: nodes =>
      c + (x - alpha) * newtonFormNested x cs nodes

lemma newtonFormAux_eq_basis_mul_nested (x : ℝ) :
    ∀ (coeffs nodes : List ℝ) (basis : ℝ),
      newtonFormAux x coeffs nodes basis =
        basis * newtonFormNested x coeffs nodes := by
  intro coeffs
  induction coeffs with
  | nil =>
      intro nodes basis
      simp [newtonFormAux, newtonFormNested]
  | cons c cs ih =>
      intro nodes basis
      cases nodes with
      | nil =>
          simp [newtonFormAux, newtonFormNested]
          ring
      | cons alpha nodes =>
          simp [newtonFormAux, newtonFormNested, ih]
          ring

/-- Equation (5.8)'s displayed sum/product Newton form is equal to the
standard nested evaluation recurrence immediately following the displayed
formula. -/
theorem newtonForm_eq_newtonFormNested
    (x : ℝ) (coeffs nodes : List ℝ) :
    newtonForm x coeffs nodes = newtonFormNested x coeffs nodes := by
  simpa [newtonForm] using
    newtonFormAux_eq_basis_mul_nested x coeffs nodes 1

end NumStability
