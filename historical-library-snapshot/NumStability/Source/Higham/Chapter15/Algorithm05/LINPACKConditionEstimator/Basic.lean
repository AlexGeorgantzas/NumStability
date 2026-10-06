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
import NumStability.Algorithms.NormEstimation.OneNorm.LINPACK.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Algorithm05 LINPACKConditionEstimator Basic

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

/-- **The LINPACK look-ahead sign choice** (Higham §15.5, Algorithm 15.5,
    the `if … ≥ …` test on p. 296).

    At column `j`, with accumulated partial products `p`, the algorithm forms the
    two candidate solution components `yⱼ⁺ = (1 − pⱼ)/uⱼⱼ`, `yⱼ⁻ = (−1 − pⱼ)/uⱼⱼ`
    and the resulting look-ahead partial products `pᵢ± = pᵢ + Uᵢⱼ yⱼ±` (`i < j`).
    It picks `dⱼ = +1` iff the weighted sum for the `+` branch dominates:
      `wⱼ|1 − pⱼ| + ∑_{i<j} wᵢ|pᵢ⁺|  ≥  wⱼ|1 + pⱼ| + ∑_{i<j} wᵢ|pᵢ⁻|`,
    otherwise `dⱼ = −1`.  (The weights `wᵢ ≥ 0`; LINPACK uses `wᵢ ≡ 1`.) -/
noncomputable def linpackSign {n : ℕ} (U : Fin n → Fin n → ℝ) (w : Fin n → ℝ) :
    Fin n → (Fin n → ℝ) → ℝ :=
  fun jk p =>
    let yplus : ℝ := (1 - p jk) / U jk jk
    let yminus : ℝ := (-1 - p jk) / U jk jk
    let lhs : ℝ := w jk * |1 - p jk| +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < jk.val),
        w i * |p i + U i jk * yplus|
    let rhs : ℝ := w jk * |(-1) - p jk| +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < jk.val),
        w i * |p i + U i jk * yminus|
    if rhs ≤ lhs then 1 else -1

/-- The LINPACK look-ahead sign rule returns `±1` (a `dⱼ` value).  This is all the
    lower-bound guarantee needs: the value of the heuristic is `±1`, whatever the
    weighted comparison decides. -/
theorem linpackSign_plusMinusOne {n : ℕ} (U : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (jk : Fin n) (p : Fin n → ℝ) :
    linpackSign U w jk p = 1 ∨ linpackSign U w jk p = -1 := by
  unfold linpackSign
  simp only
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Algorithm 15.5 solves `U y = d`.**  Immediate from `linpackD` being defined
    as the residual `U y`; recorded to match the book's step "solve `U y = d`". -/
theorem linpackY_solves {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) :
    matMulVec n U (linpackY U sgn) = linpackD U sgn := rfl

end Ch15
end NumStability
