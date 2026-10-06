-- Algorithms/CondEstimation.lean
--
-- Condition number estimation algorithms (Higham §14.1, §14.3).
--
-- Core results:
--   cond_norm_identity: ‖|A⁻¹|d‖∞ = ‖A⁻¹·diag(d)‖∞ for d ≥ 0 (eq 14.1)
--   oneNormPowerMethod: Algorithm 14.3 (1-norm power method)
--   oneNormPowerMethod_lower_bound: γ ≤ ‖A‖₁
--   lapackNormEstimator: Algorithm 14.4 (LAPACK estimator)
--   lapackNormEstimator_lower_bound: γ ≤ ‖A‖₁

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LU.GrowthFactor

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §14.1  Norm identity (eq 14.1)
-- ============================================================

/-- **Norm identity** (Higham §14.1, eq 14.1).

    For d ≥ 0 and D = diag(d):
      ‖|A⁻¹| d‖∞ = ‖A⁻¹ D‖∞.

    This reduces componentwise condition estimation (which requires |A⁻¹|)
    to a matrix norm estimation problem (which only requires A⁻¹ D).
    The key insight: when d ≥ 0, |A⁻¹_{ij}| · d_j = |A⁻¹_{ij} · d_j|,
    so the row sums coincide. -/
theorem cond_norm_identity (n : ℕ) (_hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) =
    infNorm (fun i j => A_inv i j * d j) := by
  let w : Fin n → ℝ := fun i => ∑ j : Fin n, |A_inv i j| * d j
  let B : Fin n → Fin n → ℝ := fun i j => A_inv i j * d j
  have hrow : ∀ i : Fin n, w i = ∑ j : Fin n, |B i j| := by
    intro i
    unfold w B
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul, abs_of_nonneg (hd j)]
  have hw_nonneg : ∀ i : Fin n, 0 ≤ w i := by
    intro i
    unfold w
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  change infNormVec w = infNorm B
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      rw [abs_of_nonneg (hw_nonneg i), hrow i]
      exact row_sum_le_infNorm B i
    · exact infNorm_nonneg B
  · apply infNorm_le_of_row_sum_le
    · intro i
      rw [← hrow i, ← abs_of_nonneg (hw_nonneg i)]
      exact abs_le_infNormVec w i
    · exact infNormVec_nonneg w

/-- **1-norm/∞-norm duality** (Higham §14.1, equation after 14.1).

    ‖B‖₁ = ‖Bᵀ‖∞: the 1-norm of B equals the ∞-norm of its transpose.
    This connects 1-norm condition estimation to ∞-norm problems. -/
theorem oneNorm_eq_infNorm_transpose' (n : ℕ) (_hn : 0 < n)
    (B : Fin n → Fin n → ℝ) :
    oneNorm B = infNorm (fun i j => B j i) :=
  oneNorm_eq_infNorm_transpose B

-- ============================================================
-- §14.3  1-norm power method (Algorithm 14.3)
-- ============================================================

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

/-- Standard basis vector e_j. -/
noncomputable def basisVec {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 1 else 0

/-- ‖e_j‖₁ = 1. -/
lemma oneNormVec_basisVec {n : ℕ} (j : Fin n) :
    oneNormVec (basisVec (n := n) j) = 1 := by
  simp only [oneNormVec, basisVec]
  conv_lhs =>
    arg 2; ext i
    rw [show |if i = j then (1 : ℝ) else 0| = if i = j then 1 else 0 from by
      split_ifs <;> simp]
  simp [Finset.sum_ite_eq']

/-- Index achieving the maximum of |z_j| over Fin n. -/
noncomputable def argmaxAbs {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : Fin n :=
  (Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose

/-- The argmax achieves the maximum. -/
lemma argmaxAbs_spec {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∀ j : Fin n, |z j| ≤ |z (argmaxAbs hn z)| := by
  intro j
  exact ((Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose_spec.2 j (Finset.mem_univ j))

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

-- ============================================================
-- Lower bound guarantee for Algorithm 14.3
-- ============================================================

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

/-- γ from oneNormStep is always oneNormVec of A·x, regardless of convergence. -/
private lemma oneNormStep_gamma_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n) :
    (oneNormStep hn A st).1.γ =
    oneNormVec (fun i => ∑ j : Fin n, A i j * st.x j) := by
  simp [oneNormStep]
  split_ifs <;> rfl

private lemma oneNormStep_gamma_le {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n)
    (hx : oneNormVec st.x ≤ 1) :
    (oneNormStep hn A st).1.γ ≤ oneNorm A := by
  rw [oneNormStep_gamma_eq hn A st]
  calc oneNormVec _ ≤ oneNorm A * oneNormVec st.x :=
        oneNormVec_matVec_le hn A st.x
    _ ≤ oneNorm A * 1 := mul_le_mul_of_nonneg_left hx (oneNorm_nonneg A)
    _ = oneNorm A := mul_one _

/-- oneNormStep output x satisfies ‖x‖₁ ≤ 1. -/
private lemma oneNormStep_x_le {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n)
    (hx : oneNormVec st.x ≤ 1) :
    oneNormVec (oneNormStep hn A st).1.x ≤ 1 := by
  simp only [oneNormStep]
  split_ifs
  · exact hx
  · exact le_of_eq (oneNormVec_basisVec _)

/-- The algorithm maintains ‖x‖₁ ≤ 1 and γ ≤ ‖A‖₁ as joint invariant. -/
private lemma oneNormPowerMethod_invariant {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (oneNormPowerMethod hn A fuel).x ≤ 1 ∧
    (oneNormPowerMethod hn A fuel).γ ≤ oneNorm A := by
  induction fuel with
  | zero =>
    constructor
    · simp only [oneNormPowerMethod]
      exact le_of_eq (initial_vec_oneNorm hn)
    · simp only [oneNormPowerMethod]
      have h1 := oneNormVec_matVec_le hn A (fun _ => (1 : ℝ) / ↑n)
      rw [initial_vec_oneNorm hn, mul_one] at h1
      exact h1
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    have hprev_x := ih.1
    have hprev_γ := ih.2
    -- Result is: if (oneNormStep ...).2 then prev else (oneNormStep ...).1
    -- We need to handle both cases
    set prev := oneNormPowerMethod hn A fuel with hprev_def
    set step := oneNormStep hn A prev with hstep_def
    have hstep_γ := oneNormStep_gamma_le hn A prev hprev_x
    have hstep_x := oneNormStep_x_le hn A prev hprev_x
    rw [show (let prev := oneNormPowerMethod hn A fuel;
             let x := oneNormStep hn A prev;
             if x.2 = true then prev else x.1) =
            if step.2 = true then prev else step.1 from rfl]
    split_ifs
    · exact ⟨hprev_x, hprev_γ⟩
    · exact ⟨hstep_x, hstep_γ⟩

/-- **Lower bound guarantee for Algorithm 14.3** (Higham §14.3).

    At each iteration, γ = ‖Ax‖₁ for some x with ‖x‖₁ ≤ 1,
    so γ ≤ ‖A‖₁ · ‖x‖₁ ≤ ‖A‖₁. -/
theorem oneNormPowerMethod_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    (oneNormPowerMethod hn A fuel).γ ≤ oneNorm A :=
  (oneNormPowerMethod_invariant hn A fuel).2

/-- **Algorithm 14.4** (Higham §14.3, LAPACK 1-norm estimator).

    Enhanced version of Algorithm 14.3 with:
    - Alternating starting vector b with b_i = (−1)^{i+1}(1 + (i−1)/(n−1))
    - Extra column of A evaluated at b for comparison
    - Maximum 5 iterations

    Returns a lower bound γ ≤ ‖A‖₁. -/
noncomputable def lapackAltVec {n : ℕ} (_hn : 1 < n) : Fin n → ℝ :=
  fun i => (if Even i.val then 1 else -1) *
    (1 + (i.val : ℝ) / ((n : ℝ) - 1))

/-- LAPACK norm estimator (Algorithm 14.4): run Algorithm 14.3 up to 5 iterations,
    then compare against the alternating vector estimate. -/
noncomputable def lapackNormEstimator {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  let power_est := (oneNormPowerMethod hn A 5).γ
  if h : 1 < n then
    let b := lapackAltVec h
    let alt_est := oneNormVec (fun i => ∑ j : Fin n, A i j * b j) /
                   oneNormVec b
    max power_est alt_est
  else
    power_est

/-- **Lower bound for LAPACK estimator** (Algorithm 14.4).

    The power method component satisfies γ ≤ ‖A‖₁ by
    `oneNormPowerMethod_lower_bound`. The alternating vector component
    satisfies ‖Ab‖₁/‖b‖₁ ≤ ‖A‖₁ by submultiplicativity.
    The max of two lower bounds is also a lower bound. -/
theorem lapackNormEstimator_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    lapackNormEstimator hn A ≤ oneNorm A := by
  unfold lapackNormEstimator
  split_ifs with h1n
  · apply max_le
    · exact oneNormPowerMethod_lower_bound hn A 5
    · -- ‖Ab‖₁ / ‖b‖₁ ≤ ‖A‖₁
      by_cases hb : oneNormVec (lapackAltVec h1n) = 0
      · simp [hb]; exact oneNorm_nonneg A
      · have hbpos : 0 < oneNormVec (lapackAltVec h1n) :=
          lt_of_le_of_ne (oneNormVec_nonneg _) (Ne.symm hb)
        rw [div_le_iff₀ hbpos]
        exact oneNormVec_matVec_le hn A _
  · exact oneNormPowerMethod_lower_bound hn A 5

end NumStability
