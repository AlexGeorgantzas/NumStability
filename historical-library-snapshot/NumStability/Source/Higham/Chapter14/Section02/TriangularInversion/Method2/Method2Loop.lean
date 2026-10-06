import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
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

/-!
# Chapter14 Section02 TriangularInversion Method2 Method2Loop

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Method2Loop` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- **Method 2 triangular inversion (Higham §14.2.1), concrete loop.**

    `ch14ext_method2Inv n fp L` is the matrix `X` computed by the unblocked
    reverse-column Method 2 loop applied to the lower triangular matrix `L`,
    under the standard rounding model `fp`.  Columns are computed right to
    left; because the below-diagonal update of column `j` reads only the
    already-computed trailing columns `k > j` (and the current diagonal), the
    recursion is well founded on the column index `j` (measure `n - j`).

    * strictly upper part (`i < j`): `0` (the inverse is lower triangular);
    * diagonal (`i = j`): `x_jj = fl(1 / l_jj)`, the rounded reciprocal;
    * strictly lower part (`i > j`): `x_ij = fl( (-x_jj) · fl_dotProduct(...) )`,
      i.e. the `xTRMV` dot product of trailing-submatrix row `i` with the
      below-diagonal part of column `j`, scaled by `-x_jj`.

    The `fl_dotProduct` argument masks to the strict tail `k > j`; combined with
    the lower-triangular shape of `L` this realises exactly the strict-tail
    recurrence assumed by
    `triInv_method2_left_residual_of_strict_tail_storage`. -/
noncomputable def ch14ext_method2Inv (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ
  | i, j =>
      if i.val < j.val then 0
      else if i = j then fp.fl_div 1 (L j j)
      else
        fp.fl_mul (- fp.fl_div 1 (L j j))
          (fl_dotProduct fp n
            (fun k => if j.val < k.val then ch14ext_method2Inv n fp L i k else 0)
            (fun k => L k j))
  termination_by _ j => n - j.val
  decreasing_by omega

/-- Strictly-upper entries of the Method 2 loop vanish: the computed inverse of
    a lower triangular matrix is lower triangular. -/
theorem ch14ext_method2Inv_upper (n : ℕ) (fp : FPModel) (L : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i.val < j.val) :
    ch14ext_method2Inv n fp L i j = 0 := by
  rw [ch14ext_method2Inv]
  simp [hij]

/-- Diagonal entry of the Method 2 loop: the rounded reciprocal `fl(1 / l_jj)`
    (Higham's `β̂ = α^{-1}(1+δ)`). -/
theorem ch14ext_method2Inv_diag_val (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (j : Fin n) :
    ch14ext_method2Inv n fp L j j = fp.fl_div 1 (L j j) := by
  rw [ch14ext_method2Inv]
  simp

/-- Strictly-lower entries of the Method 2 loop: the `xTRMV` dot product scaled
    by `-x_jj`, with the dot product masked to the strict column tail. -/
theorem ch14ext_method2Inv_below (n : ℕ) (fp : FPModel) (L : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : j.val < i.val) :
    ch14ext_method2Inv n fp L i j =
      fp.fl_mul (- fp.fl_div 1 (L j j))
        (fl_dotProduct fp n
          (fun k => if j.val < k.val then ch14ext_method2Inv n fp L i k else 0)
          (fun k => L k j)) := by
  have h1 : ¬ (i.val < j.val) := by omega
  have h2 : ¬ (i = j) := by
    intro h; rw [h] at hij; exact (lt_irrefl _ hij)
  rw [ch14ext_method2Inv]
  simp [h1, h2]

/-- **`hUpper`, derived.** The concrete loop produces a lower-triangular `X`. -/
theorem ch14ext_method2Inv_upper_zero (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val < j.val → ch14ext_method2Inv n fp L i j = 0 :=
  fun i j hij => ch14ext_method2Inv_upper n fp L i j hij

/-- **`hDiag`, derived from the division model.** Each diagonal entry is the
    rounded reciprocal, so `x_jj · l_jj = 1 + δ` with `|δ| ≤ u`, provided the
    diagonal of `L` is nonzero (nonsingularity — a reciprocal must exist).
    This is Higham's `β̂ α = 1 + δ`. -/
theorem ch14ext_method2Inv_diag_certificate (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (hLnonzero : ∀ j : Fin n, L j j ≠ 0) :
    ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      ch14ext_method2Inv n fp L j j * L j j = 1 + δ := by
  intro j
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div 1 (L j j) (hLnonzero j)
  refine ⟨δ, hδ, ?_⟩
  rw [ch14ext_method2Inv_diag_val n fp L j, hdiv]
  have hstep : (1 : ℝ) / L j j * (1 + δ) * L j j = (1 + δ) * (L j j / L j j) := by
    ring
  rw [hstep, div_self (hLnonzero j), mul_one]

/-- **`hStore`, derived (the headline obligation).** Every stored below-diagonal
    entry of the concrete Method 2 loop satisfies EXACTLY the strict-tail
    `fl_dotProduct`-then-`fl_mul` recurrence assumed by
    `triInv_method2_left_residual_of_strict_tail_storage`.  This is the fact
    Codex had left as a hypothesis; here it holds definitionally, the diagonal
    factor `-x_jj` being the rounded reciprocal of the current pivot. -/
theorem ch14ext_method2Inv_store (n : ℕ) (fp : FPModel) (L : Fin n → Fin n → ℝ) :
    ∀ j row : Fin n, row.val > j.val →
      ch14ext_method2Inv n fp L row j =
        fp.fl_mul (- ch14ext_method2Inv n fp L j j)
          (fl_dotProduct fp n
            (fun k => if j.val < k.val then ch14ext_method2Inv n fp L row k else 0)
            (fun k => L k j)) := by
  intro j row hij
  rw [ch14ext_method2Inv_below n fp L row j hij,
      ch14ext_method2Inv_diag_val n fp L j]

/-- **Higham Lemma 14.1 / equation (14.8) — concrete Method 2 loop,
    componentwise.**

    The inverse `X̂ = ch14ext_method2Inv n fp L` produced by the reverse-column
    Method 2 loop on a nonsingular lower triangular `L` satisfies the
    componentwise LEFT residual bound

        |X̂ L − I|_{ij} ≤ γ_{n+2} · (|X̂| |L|)_{ij}.

    The multiplier `γ_{n+2} = (n+2)u / (1 − (n+2)u)` is the honest `c_n u` form
    of Lemma 14.1, DERIVED (not assumed) by composing the loop's storage
    recurrence with Codex's
    `triInv_method2_left_residual_of_strict_tail_storage`. -/
theorem ch14ext_method2_left_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnonzero : ∀ j : Fin n, L j j ≠ 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, ch14ext_method2Inv n fp L i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2Inv n fp L i k| * |L k j| :=
  triInv_method2_left_residual_of_strict_tail_storage n fp L
    (ch14ext_method2Inv n fp L) hn2 hLT
    (ch14ext_method2Inv_diag_certificate n fp L hLnonzero)
    (ch14ext_method2Inv_upper_zero n fp L)
    (ch14ext_method2Inv_store n fp L)

/-- **Higham Lemma 14.1 / equation (14.8) — concrete Method 2 loop,
    infinity-norm.**

    Normwise companion of `ch14ext_method2_left_residual`:

        ‖X̂ L − I‖_∞ ≤ γ_{n+2} · ‖X̂‖_∞ · ‖L‖_∞ ,

    the left-residual analogue (14.8) of the Method 1 right-residual bound
    (14.4).  Everything is derived from the concrete loop and the rounding
    model; the only inputs are lower-triangular shape, nonzero diagonal, and
    the dimension guard. -/
theorem ch14ext_method2_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (L : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnonzero : ∀ j : Fin n, L j j ≠ 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, ch14ext_method2Inv n fp L i k * L k j -
        if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm (ch14ext_method2Inv n fp L) * infNorm L :=
  triInv_method2_left_residual_normwise_of_strict_tail_storage n hn0 fp L
    (ch14ext_method2Inv n fp L) hn2 hLT
    (ch14ext_method2Inv_diag_certificate n fp L hLnonzero)
    (ch14ext_method2Inv_upper_zero n fp L)
    (ch14ext_method2Inv_store n fp L)

end Ch14Ext
end NumStability
