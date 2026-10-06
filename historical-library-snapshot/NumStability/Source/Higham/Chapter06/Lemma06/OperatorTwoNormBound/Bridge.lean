import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter06.Lemma06.Core.Results
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter06 Lemma06 OperatorTwoNormBound Bridge

Canonical destination for material split out of
`NumStability.Algorithms.Ch10Ch14Lemma66Op2Bridge` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Lemma66Op2Bridge

/-- Square matrices have `rank ≤ n` (Mathlib `Matrix.rank_le_width`), recast for
the local `complexMatrixRank`. -/
theorem lemma66c_rank_le_card {n : ℕ} (B : CMatrix n n) :
    complexMatrixRank B ≤ n := by
  rw [complexMatrixRank]
  exact Matrix.rank_le_width _

/-- **Bridge / printed key inequality (Higham Lemma 6.6, used in Ch.10 (10.7) and
Ch.14 §14.3.4).**  For a square matrix `B`,

    ‖ |B| ‖₂ ≤ √n · ‖B‖₂,

where `|B| = complexAbsMatrix B` is the entrywise absolute value.  The proof
*applies* `Lemma66.lemma66_c_op2_le` to `A := |B|` (using `‖ |B|ᵢⱼ ‖ = ‖Bᵢⱼ‖`)
and then bounds `√(rank B) ≤ √n` via `lemma66c_rank_le_card`. -/
theorem lemma66c_absMatrix_op2_le_sqrt_card {n : ℕ} (hn : 0 < n) (B : CMatrix n n) :
    complexMatrixOp2 (complexAbsMatrix B) ≤ Real.sqrt (n : ℝ) * complexMatrixOp2 B := by
  have hentry : ∀ i j, ‖complexAbsMatrix B i j‖ ≤ ‖B i j‖ := fun i j =>
    le_of_eq (complexAbsMatrix_norm_apply B i j)
  refine (Lemma66.lemma66_c_op2_le hn (complexAbsMatrix B) B hentry).trans ?_
  have hrank : (complexMatrixRank B : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast lemma66c_rank_le_card B
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrank) (complexMatrixOp2_nonneg B)

end Lemma66Op2Bridge
end NumStability
