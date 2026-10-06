import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm PowerMethod CondEstimation

Canonical destination for material split out of
`NumStability.Algorithms.CondEstimation` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- 1-norm of a vector: ‖v‖₁ = ∑_i |v_i|. -/
noncomputable def oneNormVec {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |v i|

/-- 1-norm of a vector is nonneg. -/
lemma oneNormVec_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ oneNormVec v :=
  Finset.sum_nonneg (fun _i _ => abs_nonneg _)

/-- Sign vector: ξ_i = 1 if v_i ≥ 0, else −1. -/
noncomputable def signVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 ≤ v i then 1 else -1

/-- |signVec v i| = 1. -/
lemma abs_signVec {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |signVec v i| = 1 := by
  simp only [signVec]
  split_ifs <;> simp

/-- v_i · sign(v_i) = |v_i|. -/
lemma mul_signVec_eq_abs {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    v i * signVec v i = |v i| := by
  simp only [signVec]
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · push_neg at h; rw [mul_neg_one, abs_of_neg h]

/-- ‖e_j‖₁ = 1. -/
lemma oneNormVec_basisVec {n : ℕ} (j : Fin n) :
    oneNormVec (basisVec (n := n) j) = 1 := by
  simp only [oneNormVec, basisVec]
  conv_lhs =>
    arg 2; ext i
    rw [show |if i = j then (1 : ℝ) else 0| = if i = j then 1 else 0 from by
      split_ifs <;> simp]
  simp [Finset.sum_ite_eq']

/-- State for Algorithm 14.3: current iterate x, current lower bound γ. -/
structure OneNormState (n : ℕ) where
  x : Fin n → ℝ
  γ : ℝ

/-- **One step of Algorithm 14.3**.

    Given current x (with ‖x‖₁ = 1), compute:
    1. y = Ax
    2. ξ = sign(y)
    3. z = Aᵀξ
    4. γ = ‖y‖₁ = ‖Ax‖₁
    5. If ‖z‖∞ ≤ zᵀx (convergence), return (x, γ, true)
       Else j = argmax|z_j|, return (e_j, γ, false) -/
noncomputable def oneNormStep {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n) :
    OneNormState n × Bool :=
  let y := fun i => ∑ j : Fin n, A i j * st.x j      -- y = Ax
  let ξ := signVec y                                    -- ξ = sign(y)
  let z := fun j => ∑ i : Fin n, A i j * ξ i           -- z = Aᵀξ
  let γ_new := oneNormVec y                             -- γ = ‖y‖₁
  let zTx := ∑ i : Fin n, z i * st.x i                 -- zᵀx
  if infNormVec z ≤ zTx then
    (⟨st.x, γ_new⟩, true)  -- converged
  else
    let j_max := argmaxAbs hn z
    (⟨basisVec j_max, γ_new⟩, false)

/-- **Algorithm 14.3** (Higham §14.3, 1-norm power method).

    Iterates `oneNormStep` with a fuel bound. The initial vector is
    x = (1/n, …, 1/n). Returns a lower bound γ ≤ ‖A‖₁. -/
noncomputable def oneNormPowerMethod {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → OneNormState n
  | 0 =>
    let x₀ : Fin n → ℝ := fun _ => (1 : ℝ) / n
    let y₀ := fun i => ∑ j : Fin n, A i j * x₀ j
    ⟨x₀, oneNormVec y₀⟩
  | fuel + 1 =>
    let prev := oneNormPowerMethod hn A fuel
    let (next, converged) := oneNormStep hn A prev
    if converged then prev
    else next

/-- The 1-norm submultiplicativity for matrix-vector: ‖Ax‖₁ ≤ ‖A‖₁ · ‖x‖₁. -/
lemma oneNormVec_matVec_le {n : ℕ} (_hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * x j) ≤
    oneNorm A * oneNormVec x := by
  unfold oneNormVec
  -- ‖Ax‖₁ = ∑_i |∑_j A_ij x_j| ≤ ∑_i ∑_j |A_ij| |x_j|
  --        = ∑_j |x_j| ∑_i |A_ij| ≤ ∑_j |x_j| · ‖A‖₁ = ‖A‖₁ · ‖x‖₁
  calc ∑ i : Fin n, |∑ j : Fin n, A i j * x j|
      ≤ ∑ i : Fin n, ∑ j : Fin n, |A i j * x j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin n, ∑ j : Fin n, |A i j| * |x j| := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ = ∑ j : Fin n, |x j| * (∑ i : Fin n, |A i j|) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ j : Fin n, |x j| * oneNorm A := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (col_sum_le_oneNorm A j) (abs_nonneg _)
    _ = oneNorm A * ∑ j : Fin n, |x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring

/-- ‖x₀‖₁ = 1 for the initial vector x₀ = (1/n, …, 1/n) when n > 0. -/
lemma initial_vec_oneNorm {n : ℕ} (hn : 0 < n) :
    oneNormVec (fun (_ : Fin n) => (1 : ℝ) / ↑n) = 1 := by
  unfold oneNormVec
  simp only [abs_of_nonneg (div_nonneg one_nonneg (Nat.cast_nonneg' n))]
  rw [Finset.sum_const, Finset.card_fin]
  simp [Nat.pos_iff_ne_zero.mp hn]

end NumStability
