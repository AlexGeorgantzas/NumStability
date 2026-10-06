import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm LINPACK Basic

Canonical destination for material split out of
`NumStability.Algorithms.Ch15CondEstimators` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open scoped Matrix

namespace Ch15

/-- Upper-triangularity predicate: `U i j = 0` whenever `j < i`. -/
def IsUpperTriangular {n : ℕ} (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val < i.val → U i j = 0

/-- A `±1`-valued vector (the right-hand side `d` produced by Algorithm 15.5). -/
def IsPlusMinusOne {n : ℕ} (d : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, d j = 1 ∨ d j = -1

/-- `IsUpperTriangular` in the repository sense is exactly Mathlib's
    `BlockTriangular … id` on `Fin n` (both say `U i j = 0` when `j < i`). -/
theorem blockTriangular_id_of_isUpperTriangular {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsUpperTriangular U) :
    (Matrix.of U : Matrix (Fin n) (Fin n) ℝ).BlockTriangular id := by
  intro i j hji
  exact hU i j hji

/-- **Nonsingular upper triangular ⟹ nonzero diagonal.**

    An upper triangular matrix possessing a (left) inverse — i.e. a *nonsingular*
    upper triangular matrix, exactly the hypothesis of Algorithm 15.5 — has all
    diagonal entries nonzero.  This is `det U = ∏ᵢ Uᵢᵢ ≠ 0`.  It lets the
    lower-bound theorems be stated for a nonsingular upper triangular `U` with the
    `Uᵢᵢ ≠ 0` side condition *derived*, not assumed. -/
theorem diag_ne_zero_of_isUpperTriangular_isLeftInverse {n : ℕ}
    {U Uinv : Fin n → Fin n → ℝ} (hU : IsUpperTriangular U)
    (hinv : IsLeftInverse n U Uinv) :
    ∀ i : Fin n, U i i ≠ 0 := by
  -- The left inverse gives `Uinv * U = 1`, so `det U ≠ 0`.
  have hmul : (Matrix.of Uinv : Matrix (Fin n) (Fin n) ℝ) *
      (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hinv i j
  have hdet_ne : (Matrix.of U : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact one_ne_zero this.symm
  -- `det U = ∏ diagonal`, so the product is nonzero, hence each factor is.
  have hprod : (∏ i : Fin n, (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) i i) ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular
        (blockTriangular_id_of_isUpperTriangular hU)]
    exact hdet_ne
  intro i
  have := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  simpa using this

/-- The `∞`-norm of a `±1` vector is `1` (when `n > 0`). -/
theorem infNormVec_eq_one_of_plusMinusOne {n : ℕ} (hn : 0 < n)
    {d : Fin n → ℝ} (hd : IsPlusMinusOne d) :
    infNormVec d = 1 := by
  apply le_antisymm
  · -- every coordinate has `|d i| = 1 ≤ 1`
    apply infNormVec_le_of_abs_le
    · intro i
      rcases hd i with h | h <;> simp [h]
    · norm_num
  · -- coordinate `0` attains `1`
    have h0 := abs_le_infNormVec d ⟨0, hn⟩
    rcases hd ⟨0, hn⟩ with h | h <;> simp [h] at h0 <;> linarith

/-- Partial-product vector at column stage `k`: for the current partial
    solution `y` (with entries at indices `> k` already fixed), this is
      `pᵢ = ∑_{m > k} Uᵢₘ yₘ`,
    the quantity called `p(1:n)` in Algorithm 15.5 after columns `n,…,k+1`
    have been processed. -/
noncomputable def linpackPartial {n : ℕ} (U : Fin n → Fin n → ℝ)
    (k : ℕ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ m ∈ Finset.univ.filter (fun m : Fin n => k < m.val), U i m * y m

/-- One column of Algorithm 15.5, driven by an abstract sign-selection function
    `sgn`.  Column `k` (0-indexed) is processed:
    with `p = linpackPartial U k y` the accumulated partial products,
    the sign `s = sgn ⟨k,_⟩ p ∈ {±1}` is chosen (the `±1` value of `dₖ`), and
    the new component is `yₖ = (s − pₖ)/Uₖₖ` (`= (dₖ − pₖ)/uₖₖ` in the book).
    The recursion counts `k` down from `n` (columns processed right-to-left,
    exactly as the `for j = n:−1:1` loop of Algorithm 15.5). -/
noncomputable def linpackYSteps {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0,     _,  y => y
  | k + 1, hk, y =>
      let jk : Fin n := ⟨k, hk⟩
      let p : Fin n → ℝ := linpackPartial U k y
      let s : ℝ := sgn jk p
      let yk : ℝ := (s - p jk) / U jk jk
      linpackYSteps U sgn k (Nat.le_of_succ_le hk) (Function.update y jk yk)

/-- Algorithm 15.5 (LINPACK condition estimator, Higham §15.5, p. 296-297).
    Starting from `y = 0`, process all columns `n−1,…,0`.  Returns the vector `y`
    with `U y = d`, `dⱼ = ±1`, of the estimator. -/
noncomputable def linpackY {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  linpackYSteps U sgn n (le_refl n) (fun _ => 0)

/-- **The right-hand side `d = U y` of Algorithm 15.5**: the residual of the
    computed `y` under `U`.  By construction `dⱼ = ±1`. -/
noncomputable def linpackD {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  matMulVec n U (linpackY U sgn)

/-- **The LINPACK estimate is a lower bound on `‖U⁻¹‖∞` (general solve form).**

    Higham §15.5, step 3 (p. 296): "Estimate `‖T⁻¹‖ ≈ ‖x‖/‖y‖ (≤ ‖T⁻¹‖)`."

    For *any* right-hand side `d` and the exact solution `y` of `U y = d`
    (equivalently `y = U⁻¹ d`), the estimate `‖y‖∞ / ‖d‖∞` never exceeds the true
    norm `‖U⁻¹‖∞`.  This is the honest, unconditional content of the estimator:
    it follows purely from operator-norm submultiplicativity
    `‖U⁻¹ d‖∞ ≤ ‖U⁻¹‖∞ ‖d‖∞`, with no assumption on the quality of `d`.

    `Uinv` is supplied as a left inverse of `U` (`Uinv · U = I`); it then acts as
    `y = Uinv d` on the solution. -/
theorem linpack_estimate_le_infNorm_inv {n : ℕ} (hn : 0 < n)
    {U Uinv : Fin n → Fin n → ℝ} (hinv : IsLeftInverse n U Uinv)
    {y d : Fin n → ℝ} (hsolve : matMulVec n U y = d) (hd : infNormVec d ≠ 0) :
    infNormVec y / infNormVec d ≤ infNorm Uinv := by
  -- `y = Uinv (U y) = Uinv d`.
  have hyeq : y = matMulVec n Uinv d := by
    have h := matMulVec_of_isRightInverse Uinv U hinv y
    rw [hsolve] at h
    exact h.symm
  have hdpos : 0 < infNormVec d :=
    lt_of_le_of_ne (infNormVec_nonneg d) (Ne.symm hd)
  rw [div_le_iff₀ hdpos]
  calc infNormVec y = infNormVec (matMulVec n Uinv d) := by rw [hyeq]
    _ ≤ infNorm Uinv * infNormVec d := infNormVec_matMulVec_le hn Uinv d
    _ = infNorm Uinv * infNormVec d := rfl

end Ch15
end NumStability
