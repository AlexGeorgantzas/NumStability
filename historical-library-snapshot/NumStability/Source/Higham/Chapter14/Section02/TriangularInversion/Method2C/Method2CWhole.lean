import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
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
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockTriInverse
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2.Method2Loop
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.Method2C

/-!
# Chapter14 Section02 TriangularInversion Method2C Method2CWhole

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Method2CWhole` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- **Method 2C block triangular inverse (Higham §14.2.2), general N-block
    form.**

    `ch14ext_method2CInv fp bs L` is the matrix `X` computed by Method 2C on the
    lower triangular `L : Fin bs.sum → Fin bs.sum → ℝ`, where `bs : List ℕ` is
    the list of block sizes (so `n = bs.sum` and the number of blocks is
    `bs.length`).  The recursion is Higham's outer block loop:

    * `[]` (empty partition, `Fin 0`): the (vacuous) empty matrix.
    * `b :: rest`: peel the leading `b × b` block `L₁₁`; invert it by the
      concrete Method 2 loop `ch14ext_method2Inv` (Lemma 14.1); recurse Method 2C
      on the trailing `(bs.sum − b) × (bs.sum − b)` submatrix `ch14ext_blk22`;
      form the off-diagonal `(2,1)` block by the wave-2 matmul +
      back-substitution step inside `ch14ext_method2CBlockInverse`.

    Because `(b :: rest).sum` is definitionally `b + rest.sum`, the assembled
    `Fin (b + rest.sum)` matrix has exactly the ambient index type, so the
    recursion needs no index casts. -/
noncomputable def ch14ext_method2CInv (fp : FPModel) :
    (bs : List ℕ) → (L : Fin bs.sum → Fin bs.sum → ℝ) → Fin bs.sum → Fin bs.sum → ℝ
  | [], L => L
  | (b :: rest), L =>
      ch14ext_method2CBlockInverse fp b rest.sum L
        (ch14ext_method2Inv b fp (ch14ext_blk11 b rest.sum L))
        (ch14ext_method2CInv fp rest (ch14ext_blk22 b rest.sum L))

/-- Defining equation of the block Method 2C inverse at a nonempty partition:
    leading block by Method 2, trailing block by the Method 2C recursion, and
    the off-diagonal assembled by `ch14ext_method2CBlockInverse`. -/
lemma ch14ext_method2CInv_cons (fp : FPModel) (b : ℕ) (rest : List ℕ)
    (L : Fin (b + rest.sum) → Fin (b + rest.sum) → ℝ) :
    ch14ext_method2CInv fp (b :: rest) L
      = ch14ext_method2CBlockInverse fp b rest.sum L
          (ch14ext_method2Inv b fp (ch14ext_blk11 b rest.sum L))
          (ch14ext_method2CInv fp rest (ch14ext_blk22 b rest.sum L)) := rfl

/-- The leading `(1,1)` block of a matrix with nonzero diagonal has nonzero
    diagonal. -/
lemma ch14ext_m2c_blk11_diag (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hdiag : ∀ i : Fin (b + m), L i i ≠ 0) :
    ∀ a : Fin b, ch14ext_blk11 b m L a a ≠ 0 := fun _ => hdiag _

/-- The leading `(1,1)` block of a lower triangular matrix is lower triangular. -/
lemma ch14ext_m2c_blk11_lt (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hLT : ∀ i j : Fin (b + m), j.val > i.val → L i j = 0) :
    ∀ i j : Fin b, j.val > i.val → ch14ext_blk11 b m L i j = 0 := by
  intro i j h; apply hLT; simpa [ch14ext_blk11, Fin.val_castAdd] using h

/-- The trailing `(2,2)` block of a matrix with nonzero diagonal has nonzero
    diagonal. -/
lemma ch14ext_m2c_blk22_diag (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hdiag : ∀ i : Fin (b + m), L i i ≠ 0) :
    ∀ a : Fin m, ch14ext_blk22 b m L a a ≠ 0 := fun _ => hdiag _

/-- The trailing `(2,2)` block of a lower triangular matrix is lower
    triangular. -/
lemma ch14ext_m2c_blk22_lt (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hLT : ∀ i j : Fin (b + m), j.val > i.val → L i j = 0) :
    ∀ i j : Fin m, j.val > i.val → ch14ext_blk22 b m L i j = 0 := by
  intro i j h; apply hLT; simp only [Fin.val_natAdd]; omega

/-- The explicit whole-matrix Lemma 14.3 constant `cₙ = γ_{n+2} + 2γ_n + γ_n²`
    (an order-`n` multiple of `u`, matching Higham's `cₙu`). -/
noncomputable def ch14ext_m2c_const (fp : FPModel) (n : ℕ) : ℝ :=
  gamma fp (n + 2) + gamma fp n + gamma fp n + gamma fp n * gamma fp n

lemma ch14ext_m2c_const_nonneg (fp : FPModel) (n : ℕ) (hval : gammaValid fp (n + 2)) :
    0 ≤ ch14ext_m2c_const fp n := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have h1 : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hval
  have h2 : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have := mul_nonneg h2 h2
  unfold ch14ext_m2c_const
  linarith

end Ch14Ext
end NumStability
