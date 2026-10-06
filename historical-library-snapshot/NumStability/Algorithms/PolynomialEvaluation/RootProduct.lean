import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms PolynomialEvaluation RootProduct

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Exact evaluation of a polynomial from its leading coefficient and roots:
`a_n * prod_i (x - x_i)`, accumulated left to right. -/
noncomputable def rootProductEvalFrom (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], acc => acc
  | r :: roots, acc => rootProductEvalFrom x roots (acc * (x - r))

/-- Top-level exact root-product evaluation. -/
noncomputable def rootProductEval (aLeading x : ℝ) (roots : List ℝ) : ℝ :=
  rootProductEvalFrom x roots aLeading

/-- Rounded evaluation of the root-product form.  Each root contributes one
rounded subtraction and one rounded multiplication. -/
noncomputable def fl_rootProductEvalFrom (fp : FPModel) (x : ℝ) :
    List ℝ → ℝ → ℝ
  | [], acc => acc
  | r :: roots, acc =>
      fl_rootProductEvalFrom fp x roots
        (fp.fl_mul acc (fp.fl_sub x r))

/-- Top-level rounded root-product evaluation. -/
noncomputable def fl_rootProductEval
    (fp : FPModel) (aLeading x : ℝ) (roots : List ℝ) : ℝ :=
  fl_rootProductEvalFrom fp x roots aLeading

lemma rootProductEvalFrom_smul (x : ℝ) :
    ∀ (roots : List ℝ) (acc c : ℝ),
      rootProductEvalFrom x roots (acc * c) =
        rootProductEvalFrom x roots acc * c := by
  intro roots
  induction roots with
  | nil =>
      intro acc c
      simp [rootProductEvalFrom]
  | cons r roots ih =>
      intro acc c
      simp [rootProductEvalFrom, ih]
      ring

end NumStability
