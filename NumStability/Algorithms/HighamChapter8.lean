-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.

import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.TriangularArbitraryOrder
import NumStability.Algorithms.TriangularNoGuard
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.MatMul
import NumStability.Analysis.HighamChapter7
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin

namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

/-- **Algorithm 8.1**: the repository's floating-point back-substitution routine. -/
noncomputable def higham8_1_backSub (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n U b

/-- **Lemma 8.2 / Lemma 8.4, row-spec form** for Algorithm 8.1. -/
theorem higham8_2_backSub_row_spec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n) :
    BackSubRowSpec fp n U b (fl_backSub fp n U b) :=
  fl_backSub_satisfies_spec fp n U b hU hn

/-- **Lemma 8.2**, row-tight form used to prove Theorem 8.3. -/
theorem higham8_2_backSub_row_tight (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) :=
  backSub_row_tight fp n U b hU hn i

/-- **Theorem 8.3**: Algorithm 8.1 with Higham's row-specific constants. -/
theorem higham8_3_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i, |ΔU i i| ≤ gamma fp (n - i.val) * |U i i|) ∧
      (∀ i j, i.val < j.val →
        |ΔU i j| ≤ gamma fp (j.val - i.val) * |U i j|) ∧
      (∀ i j, j.val < i.val → ΔU i j = 0) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error_algorithm_8_1 fp n U b hU hUT hn

/-- **Lemma 8.4** (Higham, 2nd ed., §8.1): order-independent backward error of
`ŷ = fl((∑ wᵢ)/bₖ)` when the `n`-term sum is evaluated in *any* order (encoded by
an arbitrary summation tree `t`).  With the distinguished summand `w p`
(Higham's `c`) kept unperturbed,
`bₖ ŷ (1 + θ₀) = ∑ᵢ wᵢ (1 + θᵢ)` with every `|θ| ≤ γ_n` and `θ p = 0`.

Unlike `higham8_5_backSub_backward_error`, which fixes the repository evaluation
order, this is the sharp order-independent statement underlying Theorem 8.5.  It
is proved from the pivot-normalised summation-tree backward error
`SumTree.backward_error_pivot`. -/
theorem higham8_4_anyOrder_backwardError (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp n) (w : Fin n → ℝ) (p : Fin n)
    (bk : ℝ) (hbk : bk ≠ 0) :
    ∃ (θ₀ : ℝ) (θ : Fin n → ℝ),
      |θ₀| ≤ gamma fp n ∧
      θ p = 0 ∧
      (∀ i, |θ i| ≤ gamma fp n) ∧
      bk * fp.fl_div (t.eval fp w) bk * (1 + θ₀) = ∑ i : Fin n, w i * (1 + θ i) :=
  higham8_4_anyOrder fp t ht w p bk hbk

/-- **Theorem 8.5**, upper-triangular back-substitution specialization. -/
theorem higham8_5_backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i :=
  backSub_backward_error fp n U b hU hUT hn

/-- **Theorem 8.5**, upper-triangular back-substitution with arbitrary row
evaluation orders.  Each row supplies a summation tree for the standard
`bᵢ - Σ Uᵢⱼ*x̂ⱼ` row terms; the resulting vector solves a componentwise
perturbed upper-triangular system with Higham's `γ_n` envelope. -/
theorem higham8_5_backSub_anyOrder_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1))
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n)
    (hrow : BackSubAnyOrderSpec fp n U b xhat rowTree) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * xhat j = b i :=
  backSub_backward_error_anyOrder fp n U b xhat rowTree hU hUT hn hrow

/-- **Theorem 8.5**, lower-triangular forward-substitution specialization. -/
theorem higham8_5_forwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i :=
  forwardSub_backward_error fp n L b hL hLT hn

/-- **Theorem 8.5**, lower-triangular forward-substitution with arbitrary row
evaluation orders. -/
theorem higham8_5_forwardSub_anyOrder_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1))
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n)
    (hrow : ForwardSubAnyOrderSpec fp n L b xhat rowTree) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * xhat j = b i :=
  forwardSub_backward_error_anyOrder fp n L b xhat rowTree hL hLT hn hrow

/-! ## §8.2 Forward Error Analysis -/

/-- Internal `(8.2)` transfer: a componentwise backward-error certificate with
no right-hand-side perturbation yields the Chapter 7 relative `∞`-norm forward
bound with `cond(T, x)` and `cond(T)`. -/
private theorem higham8_relative_infNorm_bound_of_componentwise_backward_error
    (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hback : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i))
    (hLeft : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hεcond : ε * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      ε / (1 - ε * condSkeel n hn A A_inv) *
        ch7SkeelCondAtSolutionInf n hn A A_inv x := by
  rcases hback with ⟨ΔA, hΔA, hPerturbed⟩
  have hM :
      ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤
        condSkeel n hn A A_inv := by
    intro i
    unfold condSkeel
    exact
      Finset.le_sup'
        (fun i' => ∑ j : Fin n, |A_inv i' j| * ∑ k : Fin n, |A j k|)
        (Finset.mem_univ i)
  have hmain :=
    componentwise_forward_error_exact_relative_infNorm n hn A A_inv x x_hat b
      ΔA (fun _ => 0) (fun i j => |A i j|) (fun _ => 0) ε hε hΔA
      (by intro i; simp)
      (by intro i j; exact abs_nonneg _)
      (by intro i; simp)
      hLeft hAx (by simpa using hPerturbed)
      (condSkeel n hn A A_inv) hM hεcond hx
  simpa [ch7SkeelCondAtSolutionInf] using hmain

/-- **Equation (8.2)** for the repository back-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_backSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hU_diag : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hUx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn U U_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_backSub fp n U b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn U U_inv) *
        ch7SkeelCondAtSolutionInf n hn U U_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn U U_inv x (fl_backSub fp n U b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_backSub_backward_error fp n U b hU_diag hUT hγ with
      ⟨ΔU, hΔU, hPerturbed⟩
    refine ⟨ΔU, ?_, ?_⟩
    · intro i j
      simpa using hΔU i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hUx
  · exact hγcond
  · exact hx

/-- **Equation (8.2)** for the repository forward-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_forwardSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hLx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn L L_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_forwardSub fp n L b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn L L_inv) *
        ch7SkeelCondAtSolutionInf n hn L L_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn L L_inv x (fl_forwardSub fp n L b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_forwardSub_backward_error fp n L b hL_diag hLT hγ with
      ⟨ΔL, hΔL, hPerturbed⟩
    refine ⟨ΔL, ?_, ?_⟩
    · intro i j
      simpa using hΔL i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hLx
  · exact hγcond
  · exact hx

/-- **Equation (8.2)** for upper-triangular substitution with arbitrary row
evaluation orders. -/
theorem higham8_2_backSub_anyOrder_relative_infNorm_bound (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1))
    (hU_diag : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hUx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hγ : gammaValid fp n)
    (hrow : BackSubAnyOrderSpec fp n U b xhat rowTree)
    (hγcond : gamma fp n * condSkeel n hn U U_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn U U_inv) *
        ch7SkeelCondAtSolutionInf n hn U U_inv x := by
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn U U_inv x xhat b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_backSub_anyOrder_backward_error fp n U b xhat rowTree
      hU_diag hUT hγ hrow with
      ⟨ΔU, hΔU, hPerturbed⟩
    refine ⟨ΔU, ?_, ?_⟩
    · intro i j
      simpa using hΔU i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hUx
  · exact hγcond
  · exact hx

/-- **Equation (8.2)** for lower-triangular substitution with arbitrary row
evaluation orders. -/
theorem higham8_2_forwardSub_anyOrder_relative_infNorm_bound (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1))
    (hL_diag : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hLx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hγ : gammaValid fp n)
    (hrow : ForwardSubAnyOrderSpec fp n L b xhat rowTree)
    (hγcond : gamma fp n * condSkeel n hn L L_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn L L_inv) *
        ch7SkeelCondAtSolutionInf n hn L L_inv x := by
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn L L_inv x xhat b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_forwardSub_anyOrder_backward_error fp n L b xhat rowTree
      hL_diag hLT hγ hrow with
      ⟨ΔL, hΔL, hPerturbed⟩
    refine ⟨ΔL, ?_, ?_⟩
    · intro i j
      simpa using hΔL i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hLx
  · exact hγcond
  · exact hx

/-- **Equation (8.3)**: the upper-triangular stress matrix `U(α)`. -/
noncomputable def higham8_3_stressUpper (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then -α
    else 0

/-- **Equation (8.4)**: the displayed inverse-entry formula for `U(α)`. -/
noncomputable def higham8_4_stressUpperInvFormula (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then α * (1 + α) ^ (j.val - i.val - 1)
    else 0

/-- Geometric helper for the closed-form tails in the stress-matrix inverse. -/
lemma higham8_geom_one_add_mul_sum (α : ℝ) :
    ∀ m : ℕ, 1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r = (1 + α) ^ m := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ihm =>
      rw [Finset.sum_range_succ]
      calc
        1 + α * (∑ r ∈ Finset.range m, (1 + α) ^ r + (1 + α) ^ m)
            = (1 + α * ∑ r ∈ Finset.range m, (1 + α) ^ r) + α * (1 + α) ^ m := by
                ring
        _ = (1 + α) ^ m + α * (1 + α) ^ m := by
                rw [ihm]
        _ = (1 + α) ^ (m + 1) := by
                rw [pow_succ']
                ring

/-- **Equation (8.4)** support: the explicit inverse formula has column sums
`(1 + α)^j`. -/
theorem higham8_4_stressUpperInvFormula_col_sum (n : ℕ) (α : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j = (1 + α) ^ j.val := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      cases j using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          simp [higham8_4_stressUpperInvFormula]
      | succ j =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)) =
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [higham8_4_stressUpperInvFormula]
          have hhead :
              higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) =
                α * (1 + α) ^ j.val := by
            have hzero : (0 : Fin (n + 1)) ≠ Fin.succ j := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                ∑ i : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α i.succ (Fin.succ j)
                =
              α * (1 + α) ^ j.val +
                ∑ i : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [hhead, htail]
            _ = α * (1 + α) ^ j.val + (1 + α) ^ j.val := by
                  rw [ih j]
            _ = (1 + α) ^ (Fin.succ j).val := by
                  rw [show (Fin.succ j).val = j.val + 1 by rfl, pow_succ']
                  ring

/-- **Equation (8.4)** support: the explicit inverse formula has row sums
`(1 + α)^(n - 1 - i)`. -/
theorem higham8_4_stressUpperInvFormula_row_sum (n : ℕ) (α : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j =
      (1 + α) ^ (n - 1 - i.val) := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ) =
                α * ∑ j : Fin n, (1 + α) ^ j.val := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
              intro h
              exact Fin.succ_ne_zero j h.symm
            simp [higham8_4_stressUpperInvFormula, hzero]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α 0 0 +
                ∑ j : Fin n, higham8_4_stressUpperInvFormula (n + 1) α 0 j.succ
                =
              1 + α * ∑ j : Fin n, (1 + α) ^ j.val := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = 1 + α * ∑ r ∈ Finset.range n, (1 + α) ^ r := by
                  rw [Fin.sum_univ_eq_sum_range]
            _ = (1 + α) ^ n := higham8_geom_one_add_mul_sum α n
            _ = (1 + α) ^ ((n + 1) - 1 - (0 : Fin (n + 1)).val) := by
                  simp
      | succ i =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ) =
                ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [higham8_4_stressUpperInvFormula]
          calc
            higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) 0 +
                ∑ j : Fin n,
                  higham8_4_stressUpperInvFormula (n + 1) α (Fin.succ i) j.succ
                =
              ∑ j : Fin n, higham8_4_stressUpperInvFormula n α i j := by
                  rw [htail]
                  simp [higham8_4_stressUpperInvFormula]
            _ = (1 + α) ^ (n - 1 - i.val) := ih i
            _ = (1 + α) ^ ((n + 1) - 1 - (Fin.succ i).val) := by
                  have hexp : n - 1 - i.val = n - (i.val + 1) := by
                    have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
                    omega
                  simpa using congrArg (fun m : Nat => (1 + α) ^ m) hexp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine right
inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isRightInverse (n : ℕ) (α : ℝ) :
    IsRightInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    -α * ∑ k : Fin n, higham8_4_stressUpperInvFormula n α k j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                have hzero : (0 : Fin (n + 1)) ≠ k.succ := by
                  intro h
                  exact Fin.succ_ne_zero k h.symm
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzero]
              have hzeroj : (0 : Fin (n + 1)) ≠ Fin.succ j := by
                intro h
                exact Fin.succ_ne_zero j h.symm
              calc
                higham8_3_stressUpper (n + 1) α 0 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α 0 k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  α * (1 + α) ^ j.val - α * ∑ k : Fin n,
                    higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula, hzeroj]
                      ring
                _ = α * (1 + α) ^ j.val - α * (1 + α) ^ j.val := by
                      rw [higham8_4_stressUpperInvFormula_col_sum n α j]
                _ = 0 := by ring
                _ = (if (0 : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp [hzeroj]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ 0) = 0 := by
                apply Finset.sum_eq_zero
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              rw [htail]
              simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
          | succ j =>
              rw [Fin.sum_univ_succ]
              have htail :
                  (∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)) =
                    ∑ k : Fin n,
                      higham8_3_stressUpper n α i k *
                        higham8_4_stressUpperInvFormula n α k j := by
                apply Finset.sum_congr rfl
                intro k _hk
                simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
              calc
                higham8_3_stressUpper (n + 1) α (Fin.succ i) 0 *
                    higham8_4_stressUpperInvFormula (n + 1) α 0 (Fin.succ j) +
                    ∑ k : Fin n,
                      higham8_3_stressUpper (n + 1) α (Fin.succ i) k.succ *
                        higham8_4_stressUpperInvFormula (n + 1) α k.succ (Fin.succ j)
                    =
                  ∑ k : Fin n,
                    higham8_3_stressUpper n α i k *
                      higham8_4_stressUpperInvFormula n α k j := by
                      rw [htail]
                      simp [higham8_3_stressUpper, higham8_4_stressUpperInvFormula]
                _ = (if i = j then 1 else 0) := ih i j
                _ = (if (Fin.succ i : Fin (n + 1)) = Fin.succ j then 1 else 0) := by
                      simp

/-- **Equation (8.4)**: the displayed inverse-entry formula is a genuine
two-sided inverse of the stress matrix `U(α)`. -/
theorem higham8_4_stressUpperInvFormula_isInverse (n : ℕ) (α : ℝ) :
    IsInverse n (higham8_3_stressUpper n α) (higham8_4_stressUpperInvFormula n α) := by
  have hRight := higham8_4_stressUpperInvFormula_isRightInverse n α
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-! ## §8.3 Kahan's triangular example -/

/-- **Equation (8.11)**: Kahan's row-scaled triangular matrix
`U_n(θ)`, parameterized by `c = cos θ` and `s = sin θ`.

The source writes this as
`diag(1, s, ..., s^(n-1))` times a unit upper-triangular matrix with
strict upper entries `-c`. -/
noncomputable def higham8_11_kahanMatrix (n : ℕ) (c s : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => s ^ i.val * higham8_3_stressUpper n c i j

/-- **Problem 8.9** support: the leading principal block of the `(n+1) × (n+1)`
Kahan matrix is the `n × n` Kahan matrix with the same parameters.  This is the
matrix-family identity used by the Appendix A interlacing induction. -/
theorem higham8_11_kahanMatrix_leadingBlock_succ
    (n : ℕ) (c s : ℝ) (i j : Fin n) :
    higham8_11_kahanMatrix (n + 1) c s i.castSucc j.castSucc =
      higham8_11_kahanMatrix n c s i j := by
  simp [higham8_11_kahanMatrix, higham8_3_stressUpper]

/-- **Problem 8.9** support: the leading principal block of the Kahan Gram
matrix for size `n+1` is the Kahan Gram matrix for size `n`.  This is the
matrix-level input needed before applying Cauchy interlacing. -/
theorem higham8_11_kahanGram_leadingBlock_succ
    (n : ℕ) (c s : ℝ) (i j : Fin n) :
    (∑ k : Fin (n + 1),
        higham8_11_kahanMatrix (n + 1) c s k i.castSucc *
          higham8_11_kahanMatrix (n + 1) c s k j.castSucc) =
      ∑ k : Fin n,
        higham8_11_kahanMatrix n c s k i *
          higham8_11_kahanMatrix n c s k j := by
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ k : Fin n,
          higham8_11_kahanMatrix (n + 1) c s k.castSucc i.castSucc *
            higham8_11_kahanMatrix (n + 1) c s k.castSucc j.castSucc) =
        ∑ k : Fin n,
          higham8_11_kahanMatrix n c s k i *
            higham8_11_kahanMatrix n c s k j := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [higham8_11_kahanMatrix_leadingBlock_succ n c s k i,
      higham8_11_kahanMatrix_leadingBlock_succ n c s k j]
  have hlast_i :
      higham8_11_kahanMatrix (n + 1) c s (Fin.last n) i.castSucc = 0 := by
    have hne : (Fin.last n : Fin (n + 1)) ≠ i.castSucc := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    have hnlt : ¬ (n : ℕ) < i.val := by omega
    simp [higham8_11_kahanMatrix, higham8_3_stressUpper, hne, hnlt]
  rw [hsum, hlast_i]
  simp

/-- The displayed inverse-entry formula following **Equation (8.11)**:
the inverse of Kahan's matrix is the stress inverse with column `j` scaled by
`s^(-j)` in zero-based indexing. -/
noncomputable def higham8_11_kahanInvFormula (n : ℕ) (c s : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / s ^ j.val) * higham8_4_stressUpperInvFormula n c i j

/-- **Equation (8.11)** support: for `s ≠ 0`, the displayed Kahan inverse
formula is a genuine right inverse. -/
theorem higham8_11_kahanInvFormula_isRightInverse (n : ℕ) (c s : ℝ)
    (hs : s ≠ 0) :
    IsRightInverse n (higham8_11_kahanMatrix n c s)
      (higham8_11_kahanInvFormula n c s) := by
  intro i j
  have hpowj : s ^ j.val ≠ 0 := pow_ne_zero _ hs
  have hstress := higham8_4_stressUpperInvFormula_isRightInverse n c i j
  calc
    ∑ k : Fin n,
        higham8_11_kahanMatrix n c s i k *
          higham8_11_kahanInvFormula n c s k j
        =
      (s ^ i.val * (1 / s ^ j.val)) *
        ∑ k : Fin n,
          higham8_3_stressUpper n c i k *
            higham8_4_stressUpperInvFormula n c k j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          simp [higham8_11_kahanMatrix, higham8_11_kahanInvFormula]
          ring_nf
    _ = (s ^ i.val * (1 / s ^ j.val)) * (if i = j then 1 else 0) := by
          rw [hstress]
    _ = (if i = j then 1 else 0) := by
          by_cases hij : i = j
          · subst j
            simp [hs]
          · simp [hij]

/-- **Equation (8.11)** support: for `s ≠ 0`, the displayed Kahan inverse
formula is a genuine two-sided inverse. -/
theorem higham8_11_kahanInvFormula_isInverse (n : ℕ) (c s : ℝ) (hs : s ≠ 0) :
    IsInverse n (higham8_11_kahanMatrix n c s)
      (higham8_11_kahanInvFormula n c s) := by
  have hRight := higham8_11_kahanInvFormula_isRightInverse n c s hs
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-- **Problem 8.9** support: in the repository's descending singular-value
order, the second-smallest singular value of an `n × n` matrix is at zero-based
index `n - 2`. -/
def higham8_problem8_9_secondSmallestIndex (n : ℕ) (h2 : 2 ≤ n) : Fin n :=
  ⟨n - 2, by omega⟩

/-- **Problem 8.9** support: in descending order, the third-smallest slot of an
`n × n` matrix is at zero-based index `n - 3`.  This is the slot that appears
in the one-step Cauchy-interlacing reduction for the Kahan induction. -/
def higham8_problem8_9_thirdSmallestIndex (n : ℕ) (h3 : 3 ≤ n) : Fin n :=
  ⟨n - 3, by omega⟩

/-- **Problem 8.9** displayed scalar value for Kahan's matrix. -/
noncomputable def higham8_problem8_9_kahanSecondSmallestValue
    (n : ℕ) (c s : ℝ) : ℝ :=
  s ^ (n - 2) * Real.sqrt (1 + c)

private noncomputable def higham8_problem8_9_svdTopSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ
    (Set.range (fun i : {i : Fin n // i ≤ k} =>
      complexMatrixGramEigenvectorBasis A i.1))

private noncomputable def higham8_problem8_9_svdTailSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ
    (Set.range (fun i : {i : Fin n // k ≤ i} =>
      complexMatrixGramEigenvectorBasis A i.1))

private theorem higham8_problem8_9_svdTopSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_svdTopSpan A k)) = k.val + 1 := by
  rw [higham8_problem8_9_svdTopSpan]
  rw [finrank_span_eq_card]
  · convert (Fintype.card_Iic k).trans (Fin.card_Iic k) using 2
  · exact (complexMatrixGramEigenvectorBasis A).toBasis.linearIndependent.comp
      (fun i : {i : Fin n // i ≤ k} => (i : Fin n))
      (Subtype.val_injective)

private theorem higham8_problem8_9_svdTailSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_svdTailSpan A k)) = n - k.val := by
  rw [higham8_problem8_9_svdTailSpan]
  rw [finrank_span_eq_card]
  · convert (Fintype.card_Ici k).trans (Fin.card_Ici k) using 2
  · exact (complexMatrixGramEigenvectorBasis A).toBasis.linearIndependent.comp
      (fun i : {i : Fin n // k ≤ i} => (i : Fin n))
      (Subtype.val_injective)

private theorem higham8_problem8_9_svdTopSpan_repr_eq_zero_of_lt
    {n : ℕ} (A : CMatrix n n) (k j : Fin n)
    {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTopSpan A k) (hkj : k < j) :
    (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
  rw [higham8_problem8_9_svdTopSpan] at hx
  refine Submodule.span_induction
    (s := Set.range (fun i : {i : Fin n // i ≤ k} =>
      complexMatrixGramEigenvectorBasis A i.1))
    ?mem ?zero ?add ?smul hx
  · rintro y ⟨i, rfl⟩
    have hji : j ≠ (i : Fin n) := by
      intro h
      subst j
      exact not_lt_of_ge i.2 hkj
    simp [OrthonormalBasis.repr_self, hji]
  · simp
  · intro x y hx hy hx0 hy0
    simp [map_add, hx0, hy0]
  · intro a x hx hx0
    simp [map_smul, hx0]

private theorem higham8_problem8_9_svdTailSpan_repr_eq_zero_of_lt
    {n : ℕ} (A : CMatrix n n) (k j : Fin n)
    {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTailSpan A k) (hjk : j < k) :
    (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
  rw [higham8_problem8_9_svdTailSpan] at hx
  refine Submodule.span_induction
    (s := Set.range (fun i : {i : Fin n // k ≤ i} =>
      complexMatrixGramEigenvectorBasis A i.1))
    ?mem ?zero ?add ?smul hx
  · rintro y ⟨i, rfl⟩
    have hji : j ≠ (i : Fin n) := by
      intro h
      subst j
      exact not_lt_of_ge i.2 hjk
    simp [OrthonormalBasis.repr_self, hji]
  · simp
  · intro x y hx hy hx0 hy0
    simp [map_add, hx0, hy0]
  · intro a x hx hx0
    simp [map_smul, hx0]

private theorem higham8_problem8_9_matrix_toEuclideanLin_ofLp
    {m n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    WithLp.ofLp (Matrix.toEuclideanLin A x) =
      Matrix.toLin' A (WithLp.ofLp x) := by
  change WithLp.ofLp (((Matrix.toLpLin (2 : ENNReal) (2 : ENNReal)) A) x) =
    Matrix.toLin' A (WithLp.ofLp x)
  exact Matrix.ofLp_toLpLin (2 : ENNReal) (2 : ENNReal) A x

private theorem higham8_problem8_9_norm_sq_eq_sum
    {n : ℕ} (A : CMatrix n n) (z : EuclideanSpace ℂ (Fin n)) :
    ‖complexMatrixEuclideanLin A z‖ ^ 2 =
      ∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr z i‖ ^ 2 := by
  classical
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension A
  let q : Equiv.Perm (Fin n) := complexMatrixLeftSingularVectorBasisPerm A b hcontains
  let coeff : EuclideanSpace ℂ (Fin n) := (complexMatrixGramEigenvectorBasis A).repr z
  have hcoord :
      Matrix.mulVec (highamProblem65MonomialMatrix q
          (fun i => (complexMatrixSingularValue A i : ℂ))) coeff =
        b.repr (complexMatrixEuclideanLin A z) := by
    have h := complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr A b hcontains z
    rw [complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_basisPerm A b hcontains] at h
    simpa [q, coeff] using h
  have hcoord_lift :
      (WithLp.toLp (2 : ENNReal)
        (Matrix.mulVec (highamProblem65MonomialMatrix q
          (fun i => (complexMatrixSingularValue A i : ℂ)))
          (WithLp.ofLp coeff)) : EuclideanSpace ℂ (Fin n)) =
        b.repr (complexMatrixEuclideanLin A z) := by
    apply WithLp.ofLp_injective
    simpa [q, coeff] using hcoord
  have hnorm_repr :
      ‖b.repr (complexMatrixEuclideanLin A z)‖ =
        ‖complexMatrixEuclideanLin A z‖ :=
    LinearIsometryEquiv.norm_map b.repr (complexMatrixEuclideanLin A z)
  rw [← hnorm_repr, ← hcoord_lift]
  exact ch7Problem75_monomial_mulVec_norm_sq_eq_sum q
    (fun i => complexMatrixSingularValue A i) coeff

private theorem higham8_problem8_9_topSpan_sigma_mul_norm_le
    {n : ℕ} (A : CMatrix n n) (k : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTopSpan A k) :
    complexMatrixSingularValue A k * ‖x‖ ≤ ‖complexMatrixEuclideanLin A x‖ := by
  apply (sq_le_sq₀
    (mul_nonneg (complexMatrixSingularValue_nonneg A k) (norm_nonneg x))
    (norm_nonneg (complexMatrixEuclideanLin A x))).mp
  rw [mul_pow, higham8_problem8_9_norm_sq_eq_sum]
  calc
    complexMatrixSingularValue A k ^ 2 * ‖x‖ ^ 2
        = ∑ i : Fin n,
            complexMatrixSingularValue A k ^ 2 *
              ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          rw [← ch7Problem75_orthonormalBasis_repr_norm_sq
            (complexMatrixGramEigenvectorBasis A) x]
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hki : k < i
          · have hzero :=
              higham8_problem8_9_svdTopSpan_repr_eq_zero_of_lt A k i hx hki
            simp [hzero]
          · have hik : i ≤ k := le_of_not_gt hki
            exact mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (complexMatrixSingularValue_nonneg A k)
                (complexMatrixSingularValue_nonneg A i)).mpr
                (complexMatrixSingularValue_antitone A hik))
              (sq_nonneg _)

private theorem higham8_problem8_9_tailSpan_norm_image_le_sigma_mul_norm
    {n : ℕ} (A : CMatrix n n) (k : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTailSpan A k) :
    ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A k * ‖x‖ := by
  apply (sq_le_sq₀
    (norm_nonneg (complexMatrixEuclideanLin A x))
    (mul_nonneg (complexMatrixSingularValue_nonneg A k) (norm_nonneg x))).mp
  rw [mul_pow, higham8_problem8_9_norm_sq_eq_sum]
  calc
    (∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2)
        ≤ ∑ i : Fin n,
            complexMatrixSingularValue A k ^ 2 *
              ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hik : i < k
          · have hzero :=
              higham8_problem8_9_svdTailSpan_repr_eq_zero_of_lt A k i hx hik
            simp [hzero]
          · have hki : k ≤ i := le_of_not_gt hik
            exact mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (complexMatrixSingularValue_nonneg A i)
                (complexMatrixSingularValue_nonneg A k)).mpr
                (complexMatrixSingularValue_antitone A hki))
              (sq_nonneg _)
    _ = complexMatrixSingularValue A k ^ 2 * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum]
          rw [ch7Problem75_orthonormalBasis_repr_norm_sq]

private noncomputable def higham8_problem8_9_embedLastZero (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)) where
  toFun x := WithLp.toLp (2 : ENNReal)
    (fun i : Fin (n + 1) => if h : i.val < n then WithLp.ofLp x ⟨i.val, h⟩ else 0)
  map_add' x y := by
    apply WithLp.ofLp_injective
    ext i
    by_cases h : i.val < n <;> simp [h]
  map_smul' a x := by
    apply WithLp.ofLp_injective
    ext i
    by_cases h : i.val < n <;> simp [h]

@[simp] private theorem higham8_problem8_9_embedLastZero_apply_castSucc
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    higham8_problem8_9_embedLastZero n x i.castSucc = x i := by
  simp [higham8_problem8_9_embedLastZero]

@[simp] private theorem higham8_problem8_9_embedLastZero_apply_last
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    higham8_problem8_9_embedLastZero n x (Fin.last n) = 0 := by
  simp [higham8_problem8_9_embedLastZero]

private theorem higham8_problem8_9_embedLastZero_norm
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖higham8_problem8_9_embedLastZero n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp [higham8_problem8_9_embedLastZero]

private theorem higham8_problem8_9_embedLastZero_injective (n : ℕ) :
    Function.Injective (higham8_problem8_9_embedLastZero n) := by
  intro x y hxy
  apply WithLp.ofLp_injective
  ext i
  have hcoord :=
    congrArg (fun z : EuclideanSpace ℂ (Fin (n + 1)) => z i.castSucc) hxy
  simpa using hcoord

private theorem higham8_problem8_9_kahan_euclideanLin_embed
    (n : ℕ) (c s : ℝ) (x : EuclideanSpace ℂ (Fin n)) :
    complexMatrixEuclideanLin
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_embedLastZero n x) =
      higham8_problem8_9_embedLastZero n
        (complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s)) x) := by
  apply WithLp.ofLp_injective
  ext r
  refine Fin.lastCases ?last ?cast r
  · simp only [complexMatrixEuclideanLin]
    rw [higham8_problem8_9_matrix_toEuclideanLin_ofLp]
    change Matrix.toLin' (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (WithLp.ofLp ((higham8_problem8_9_embedLastZero n) x)) (Fin.last n) =
      WithLp.ofLp ((higham8_problem8_9_embedLastZero n)
        ((complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))) x)) (Fin.last n)
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_castSucc]
    simp [higham8_problem8_9_embedLastZero]
    apply Finset.sum_eq_zero
    intro j _hj
    have hne : Fin.last n ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    have hnlt : ¬ n < j.val := by omega
    simp [realRectToCMatrix, higham8_11_kahanMatrix, higham8_3_stressUpper, hne, hnlt]
  · intro i
    simp only [complexMatrixEuclideanLin]
    rw [higham8_problem8_9_matrix_toEuclideanLin_ofLp]
    change Matrix.toLin' (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (WithLp.ofLp ((higham8_problem8_9_embedLastZero n) x)) i.castSucc =
      WithLp.ofLp ((higham8_problem8_9_embedLastZero n)
        ((complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))) x)) i.castSucc
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_castSucc]
    simp [higham8_problem8_9_embedLastZero, realRectToCMatrix,
      higham8_11_kahanMatrix_leadingBlock_succ]
    rfl

private noncomputable def higham8_problem8_9_embeddedTopSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
  LinearMap.range
    ((higham8_problem8_9_embedLastZero n).comp
      (higham8_problem8_9_svdTopSpan A k).subtype)

private theorem higham8_problem8_9_embeddedTopSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_embeddedTopSpan A k)) = k.val + 1 := by
  rw [higham8_problem8_9_embeddedTopSpan]
  rw [LinearMap.finrank_range_of_inj]
  · exact higham8_problem8_9_svdTopSpan_finrank A k
  · intro x y hxy
    apply Subtype.ext
    exact higham8_problem8_9_embedLastZero_injective n hxy

private theorem higham8_problem8_9_subspace_intersection_nonzero
    {N dS dT : ℕ}
    (S T : Submodule ℂ (EuclideanSpace ℂ (Fin N)))
    (hS : Module.finrank ℂ (↥S) = dS)
    (hT : Module.finrank ℂ (↥T) = dT)
    (hsum : N < dS + dT) :
    ∃ x : EuclideanSpace ℂ (Fin N), x ∈ S ∧ x ∈ T ∧ x ≠ 0 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hsup_le : Module.finrank ℂ (↥(S ⊔ T)) ≤ N := by
    calc
      Module.finrank ℂ (↥(S ⊔ T)) ≤
          Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) :=
        Submodule.finrank_le (S ⊔ T)
      _ = N := finrank_euclideanSpace_fin
  have hinf_pos : 0 < Module.finrank ℂ (↥(S ⊓ T)) := by
    rw [hS, hT] at hdim
    omega
  have hne : S ⊓ T ≠ ⊥ := by
    intro hbot
    have hfin : Module.finrank ℂ (↥(S ⊓ T)) = 0 := by
      rw [hbot, finrank_bot]
    omega
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff (S ⊓ T)).1 hne
  rw [Submodule.mem_inf] at hx
  exact ⟨x, hx.1, hx.2, hxne⟩

private theorem higham8_problem8_9_kahanSingularValue_interlace_succ
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)) := by
  classical
  let B : CMatrix n n := realRectToCMatrix (higham8_11_kahanMatrix n c s)
  let A : CMatrix (n + 1) (n + 1) :=
    realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s)
  let k := higham8_problem8_9_secondSmallestIndex n h2
  let r := higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega : 3 ≤ n + 1)
  by_contra hnot
  have hlt : complexMatrixSingularValue A r < complexMatrixSingularValue B k :=
    lt_of_not_ge hnot
  let S := higham8_problem8_9_embeddedTopSpan B k
  let T := higham8_problem8_9_svdTailSpan A r
  have hSdim : Module.finrank ℂ (↥S) = n - 1 := by
    have hkval : k.val + 1 = n - 1 := by
      simp [k, higham8_problem8_9_secondSmallestIndex]
      omega
    rw [higham8_problem8_9_embeddedTopSpan_finrank B k, hkval]
  have hTdim : Module.finrank ℂ (↥T) = 3 := by
    have hrval : (n + 1) - r.val = 3 := by
      simp [r, higham8_problem8_9_thirdSmallestIndex]
      omega
    rw [higham8_problem8_9_svdTailSpan_finrank A r, hrval]
  obtain ⟨x, hxS, hxT, hxne⟩ :=
    higham8_problem8_9_subspace_intersection_nonzero S T hSdim hTdim (by omega)
  rcases hxS with ⟨yTop, hyEq⟩
  let y : EuclideanSpace ℂ (Fin n) := yTop
  have hyTop : y ∈ higham8_problem8_9_svdTopSpan B k := yTop.property
  have hxy : higham8_problem8_9_embedLastZero n y = x := by
    simpa [S, higham8_problem8_9_embeddedTopSpan, y] using hyEq
  have hyne : y ≠ 0 := by
    intro hy0
    apply hxne
    rw [← hxy, hy0]
    simp
  have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have hlower : complexMatrixSingularValue B k * ‖y‖ ≤
      ‖complexMatrixEuclideanLin B y‖ :=
    higham8_problem8_9_topSpan_sigma_mul_norm_le B k hyTop
  have haction :
      ‖complexMatrixEuclideanLin A (higham8_problem8_9_embedLastZero n y)‖ =
        ‖complexMatrixEuclideanLin B y‖ := by
    rw [higham8_problem8_9_kahan_euclideanLin_embed]
    exact higham8_problem8_9_embedLastZero_norm n (complexMatrixEuclideanLin B y)
  have hupper_x :
      ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A r * ‖x‖ :=
    higham8_problem8_9_tailSpan_norm_image_le_sigma_mul_norm A r hxT
  have hupper :
      ‖complexMatrixEuclideanLin B y‖ ≤ complexMatrixSingularValue A r * ‖y‖ := by
    rw [← haction, hxy]
    calc
      ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A r * ‖x‖ :=
        hupper_x
      _ = complexMatrixSingularValue A r * ‖y‖ := by
            rw [← hxy, higham8_problem8_9_embedLastZero_norm]
  have hle_mul : complexMatrixSingularValue B k * ‖y‖ ≤
      complexMatrixSingularValue A r * ‖y‖ := hlower.trans hupper
  have hlt_mul : complexMatrixSingularValue A r * ‖y‖ <
      complexMatrixSingularValue B k * ‖y‖ :=
    mul_lt_mul_of_pos_right hlt hynorm_pos
  exact not_lt_of_ge hle_mul hlt_mul

private theorem higham8_problem8_9_kahanGram_interlace_succ
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)) := by
  have hsing := higham8_problem8_9_kahanSingularValue_interlace_succ n h2 c s
  have hsq := (sq_le_sq₀
    (complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix n c s))
      (higham8_problem8_9_secondSmallestIndex n h2))
    (complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
      (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)))).mpr hsing
  rw [complexMatrixSingularValue_sq, complexMatrixSingularValue_sq] at hsq
  exact hsq

/-- **Problem 8.9**, Kahan-specific leading-block interlacing step.

This is the ordered Gram-eigenvalue inequality used by Appendix A's induction:
the previous-size second-smallest Gram eigenvalue is bounded by the current
third-smallest Gram eigenvalue.  The proof uses the right singular-vector
top span for the leading block, the tail span for the current matrix, and a
dimension-count intersection after embedding the leading block by appending
one zero coordinate. -/
theorem higham8_problem8_9_kahanGram_interlacing (c s : ℝ) :
    ∀ (m : ℕ) (hm : 3 ≤ m),
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
          (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix m c s))
          (higham8_problem8_9_thirdSmallestIndex m hm) := by
  intro m hm
  rcases m with _ | _ | _ | k
  · omega
  · omega
  · omega
  · have h := higham8_problem8_9_kahanGram_interlace_succ (k + 2) (by omega) c s
    simpa [Nat.add_assoc] using h

private theorem higham8_complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self_scalar
    {n : ℕ} (A : CMatrix n n) (lam : ℂ)
    (hA : (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
      (lam • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    complexMatrixGramLin A =
      lam •
        (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
  let b := complexEuclideanBasisFin n
  rw [← Matrix.toLin_toMatrix b b (complexMatrixGramLin A)]
  rw [← Matrix.toLin_toMatrix b b
    (lam •
      (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))]
  congr 1
  rw [complexMatrixGramLin_toMatrix, hA]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply]
  · simp [LinearMap.toMatrix_apply, hij]

private theorem higham8_complexMatrixGramEigenvalues_eq_of_gramLin_eq_smul_id
    {m n : ℕ} (A : CMatrix m n) {lam : ℝ}
    (h :
      complexMatrixGramLin A =
        ((lam : ℂ) •
          (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))) :
    ∀ i : Fin n, complexMatrixGramEigenvalues A i = lam := by
  intro i
  let b := complexMatrixGramEigenvectorBasis A
  let v : EuclideanSpace ℂ (Fin n) := b i
  have heig := complexMatrixGramLin_apply_eigenvectorBasis A i
  have hsmul : ((lam : ℂ) • v) = (complexMatrixGramEigenvalues A i : ℂ) • v := by
    simpa [v, b, h, LinearMap.smul_apply] using heig
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvn : ‖v‖ = 1 := by
      simp [v, b, complexMatrixGramEigenvectorBasis_norm A i]
    simp [hv] at hvn
  have hzero : (((lam : ℂ) - (complexMatrixGramEigenvalues A i : ℂ)) • v) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hsmul
  have hscalar : (lam : ℂ) - (complexMatrixGramEigenvalues A i : ℂ) = 0 := by
    exact (smul_eq_zero.mp hzero).resolve_right hv_ne
  apply Complex.ofReal_injective
  exact (sub_eq_zero.mp hscalar).symm

theorem higham8_11_kahanMatrix_zero_one_eq_finiteId (n : ℕ) :
    higham8_11_kahanMatrix n 0 1 = (finiteIdMatrix : Fin n → Fin n → ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [higham8_11_kahanMatrix, higham8_3_stressUpper, finiteIdMatrix]
  · simp [higham8_11_kahanMatrix, higham8_3_stressUpper, finiteIdMatrix, hij]

theorem higham8_problem8_9_kahan_zero_one_gramEigenvalues_eq_one
    (n : ℕ) :
    ∀ i : Fin n,
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n 0 1)) i = 1 := by
  apply higham8_complexMatrixGramEigenvalues_eq_of_gramLin_eq_smul_id
  apply higham8_complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self_scalar
  have hA :
      complexCMatrixAsMatrix (realRectToCMatrix (higham8_11_kahanMatrix n 0 1)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [higham8_11_kahanMatrix_zero_one_eq_finiteId n]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [complexCMatrixAsMatrix, realRectToCMatrix, finiteIdMatrix]
    · simp [complexCMatrixAsMatrix, realRectToCMatrix, finiteIdMatrix, hij]
  rw [hA]
  simp

theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_one
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs_one : s = 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  subst s
  have hc_sq : c ^ 2 = 0 := by nlinarith
  have hc_zero : c = 0 := sq_eq_zero_iff.mp hc_sq
  subst c
  have hgram :=
    higham8_problem8_9_kahan_zero_one_gramEigenvalues_eq_one n
      (higham8_problem8_9_secondSmallestIndex n h2)
  simpa using hgram

/-- **Problem 8.9**, SVD/Gram reduction.

The remaining hard step is the spectral statement that the Kahan Gram
eigenvalue at index `n - 2` is `s^(2(n-2)) (1+c)`.  This theorem discharges the
source's singular-value formula from exactly that Gram-eigenvalue certificate,
including the scalar square-root algebra under `c, s ≥ 0`. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hgram :
      complexMatrixGramEigenvalues (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2) =
        (s ^ (n - 2)) ^ 2 * (1 + c)) :
    complexMatrixSingularValue (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply (sq_eq_sq₀
    (complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix n c s))
      (higham8_problem8_9_secondSmallestIndex n h2))
    (mul_nonneg (pow_nonneg hs _) (Real.sqrt_nonneg _))).mp
  rw [complexMatrixSingularValue_sq, hgram]
  rw [mul_pow, Real.sq_sqrt (by linarith)]

theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_one : s = 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc
  · rw [hs_one]
    norm_num
  · exact
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_one
        n h2 c s hcs hs_one

/-- **Problem 8.9** support: the last index of the `n × n` Kahan matrix. -/
def higham8_problem8_9_lastIndex (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- **Problem 8.9** support: the last ordered singular value is bounded above
by any test-vector quotient.  This is the local minimum-singular-value half
needed for Appendix A's line `σ_n(U_n(θ)) ≤ s^(n-1)`. -/
theorem higham8_problem8_9_lastSingularValue_mul_norm_le_image_norm
    {n : ℕ} (hn : 0 < n) (A : CMatrix n n)
    (z : EuclideanSpace ℂ (Fin n)) :
    complexMatrixSingularValue A (higham8_problem8_9_lastIndex n hn) * ‖z‖ ≤
      ‖complexMatrixEuclideanLin A z‖ := by
  classical
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension A
  refine
    problem7_5_sigmaMin_mul_norm_le_image_norm A b hcontains z
      (complexMatrixSingularValue_nonneg A (higham8_problem8_9_lastIndex n hn))
      ?_
  intro i
  exact complexMatrixSingularValue_antitone A
    (Fin.le_iff_val_le_val.2 (by
      simp [higham8_problem8_9_lastIndex]
      omega))

/-- **Problem 8.9** support: real square-matrix version of the test-vector
upper bound for the smallest ordered singular value. -/
theorem higham8_problem8_9_lastSingularValue_mul_vecNorm_le_matMulVec_norm
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) (z : Fin n → ℝ) :
    complexMatrixSingularValue (realRectToCMatrix A)
        (higham8_problem8_9_lastIndex n hn) * vecNorm2 z ≤
      vecNorm2 (matMulVec n A z) := by
  have h :=
    higham8_problem8_9_lastSingularValue_mul_norm_le_image_norm
      (n := n) hn (A := realRectToCMatrix A) (z := realVecToEuclidean z)
  rw [realVecToEuclidean_norm] at h
  rw [realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] at h
  simpa [matMulVec, rectMatMulVec] using h

/-- **Problem 8.9** support: the unscaled last column of the stress inverse is
sent by Kahan's matrix to `s^(n-1)` times the last coordinate vector. -/
theorem higham8_problem8_9_kahan_stressInvLastColumn_action
    (n : ℕ) (hn : 0 < n) (c s : ℝ) :
    matMulVec n (higham8_11_kahanMatrix n c s)
        (fun k => higham8_4_stressUpperInvFormula n c k
          (higham8_problem8_9_lastIndex n hn)) =
      fun i => s ^ (n - 1) *
        finiteBasisVec (higham8_problem8_9_lastIndex n hn) i := by
  let q := higham8_problem8_9_lastIndex n hn
  have hstress := higham8_4_stressUpperInvFormula_isRightInverse n c
  ext i
  unfold matMulVec
  calc
    (∑ k : Fin n,
        higham8_11_kahanMatrix n c s i k *
          higham8_4_stressUpperInvFormula n c k q)
        =
      s ^ i.val *
        ∑ k : Fin n,
          higham8_3_stressUpper n c i k *
            higham8_4_stressUpperInvFormula n c k q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          simp [higham8_11_kahanMatrix]
          ring
    _ = s ^ i.val * (if i = q then 1 else 0) := by
          rw [hstress i q]
    _ = s ^ (n - 1) * finiteBasisVec q i := by
          by_cases hiq : i = q
          · subst i
            simp [q, higham8_problem8_9_lastIndex, finiteBasisVec]
          · simp [finiteBasisVec, hiq]

/-- **Problem 8.9** support: Appendix A's upper bound on the smallest singular
value of Kahan's matrix, `σ_n(U_n(θ)) ≤ s^(n-1)`, in zero-based local order. -/
theorem higham8_problem8_9_kahan_smallestSingularValue_le_pow
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) (hs : 0 ≤ s) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_lastIndex n (by omega)) ≤
      s ^ (n - 1) := by
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  let z : Fin n → ℝ := fun k => higham8_4_stressUpperInvFormula n c k q
  have hz_norm_ge : 1 ≤ vecNorm2 z := by
    have hcoord := abs_coord_le_vecNorm2 z q
    simpa [z, q, higham8_4_stressUpperInvFormula] using hcoord
  have haction :
      matMulVec n (higham8_11_kahanMatrix n c s) z =
        fun i => s ^ (n - 1) * finiteBasisVec q i := by
    simpa [z, q] using
      higham8_problem8_9_kahan_stressInvLastColumn_action
        n (by omega : 0 < n) c s
  have himage :
      vecNorm2 (matMulVec n (higham8_11_kahanMatrix n c s) z) =
        s ^ (n - 1) := by
    rw [haction, vecNorm2_smul, ch7Problem79_vecNorm2_finiteBasisVec]
    rw [abs_of_nonneg (pow_nonneg hs _), mul_one]
  have htest :=
    higham8_problem8_9_lastSingularValue_mul_vecNorm_le_matMulVec_norm
      (n := n) (by omega : 0 < n) (higham8_11_kahanMatrix n c s) z
  have hσ_nonneg :
      0 ≤ complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s)) q :=
    complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix n c s)) q
  calc
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s)) q
        =
      complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s)) q * 1 := by ring
    _ ≤
      complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s)) q * vecNorm2 z :=
        mul_le_mul_of_nonneg_left hz_norm_ge hσ_nonneg
    _ ≤ vecNorm2 (matMulVec n (higham8_11_kahanMatrix n c s) z) := htest
    _ = s ^ (n - 1) := himage

/-- **Problem 8.9** support: in Appendix A's `0 < s < 1` branch, the
smallest singular value lies strictly below the displayed candidate.  The
remaining source step is therefore only the interlacing induction that puts a
larger singular value before the candidate. -/
theorem higham8_problem8_9_kahan_smallestSingularValue_lt_candidate
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_lastIndex n (by omega)) <
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hsmall :=
    higham8_problem8_9_kahan_smallestSingularValue_le_pow n h2 c s hs_nonneg
  have hsqrt_ge_one : 1 ≤ Real.sqrt (1 + c) := by
    have hle : (1 : ℝ) ≤ 1 + c := by linarith
    simpa using Real.sqrt_le_sqrt hle
  have hs_lt_sqrt : s < Real.sqrt (1 + c) := lt_of_lt_of_le hs_lt hsqrt_ge_one
  have hpow_pos : 0 < s ^ (n - 2) := pow_pos hs_pos _
  have hidx : n - 1 = n - 2 + 1 := by omega
  calc
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_lastIndex n (by omega))
        ≤ s ^ (n - 1) := hsmall
    _ = s ^ (n - 2) * s := by rw [hidx, pow_succ]
    _ < s ^ (n - 2) * Real.sqrt (1 + c) :=
        mul_lt_mul_of_pos_left hs_lt_sqrt hpow_pos
    _ = higham8_problem8_9_kahanSecondSmallestValue n c s := rfl

/-- **Problem 8.9** support: in Appendix A's `0 < s < 1` branch, the
smallest Gram eigenvalue lies strictly below the displayed Gram candidate. -/
theorem higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_lastIndex n (by omega)) <
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  let A : CMatrix n n := realRectToCMatrix (higham8_11_kahanMatrix n c s)
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  let σ := higham8_problem8_9_kahanSecondSmallestValue n c s
  let lam : ℝ := (s ^ (n - 2)) ^ 2 * (1 + c)
  have hσ_nonneg : 0 ≤ σ := by
    exact mul_nonneg (pow_nonneg (le_of_lt hs_pos) _) (Real.sqrt_nonneg _)
  have hsmall :
      complexMatrixSingularValue A q < σ := by
    simpa [A, q, σ] using
      higham8_problem8_9_kahan_smallestSingularValue_lt_candidate
        n h2 c s hc hs_pos hs_lt
  have hsq :
      complexMatrixSingularValue A q ^ 2 < σ ^ 2 :=
    (sq_lt_sq₀ (complexMatrixSingularValue_nonneg A q) hσ_nonneg).2 hsmall
  have hσ_sq : σ ^ 2 = lam := by
    simp [σ, lam, higham8_problem8_9_kahanSecondSmallestValue, mul_pow,
      Real.sq_sqrt (by linarith : 0 ≤ 1 + c)]
  rw [complexMatrixSingularValue_sq, hσ_sq] at hsq
  simpa [A, q, lam] using hsq

/-- **Problem 8.9** support: a scaled right witness vector for Zha's
Appendix A singular-vector calculation.  It is supported on the last two
coordinates and is scaled by `sqrt (1+c)` to avoid denominator bookkeeping. -/
noncomputable def higham8_problem8_9_kahanRightWitness
    (n : ℕ) (h2 : 2 ≤ n) (c : ℝ) : Fin n → ℝ :=
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega)
  fun i =>
    if i = p then Real.sqrt (1 + c)
    else if i = q then -Real.sqrt (1 + c)
    else 0

/-- **Problem 8.9** support: the right Kahan witness is nonzero under the
source-side assumption `0 ≤ c`. -/
theorem higham8_problem8_9_kahanRightWitness_euclidean_ne_zero
    (n : ℕ) (h2 : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c) ≠ 0 := by
  let p := higham8_problem8_9_secondSmallestIndex n h2
  have hp :
      higham8_problem8_9_kahanRightWitness n h2 c p =
        Real.sqrt (1 + c) := by
    simp [higham8_problem8_9_kahanRightWitness, p]
  have hsqrt_pos : 0 < Real.sqrt (1 + c) :=
    Real.sqrt_pos.2 (by linarith)
  intro hzero
  have hfun :
      (fun j : Fin n =>
          (higham8_problem8_9_kahanRightWitness n h2 c j : ℂ)) = 0 := by
    have h := congrArg WithLp.ofLp hzero
    simpa [realVecToEuclidean] using h
  have hp_zero :
      (higham8_problem8_9_kahanRightWitness n h2 c p : ℂ) = 0 := by
    exact congrFun hfun p
  rw [hp] at hp_zero
  exact (Complex.ofReal_ne_zero.mpr hsqrt_pos.ne') hp_zero

/-- **Problem 8.9** support: a scaled left witness vector for Zha's Appendix A
singular-vector calculation. -/
noncomputable def higham8_problem8_9_kahanLeftWitness
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) : Fin n → ℝ :=
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega)
  fun i =>
    if i = p then 1 + c
    else if i = q then -s
    else 0

private theorem higham8_sum_two_support {n : ℕ}
    (p q : Fin n) (hpq : p ≠ q) (f : Fin n → ℝ) (a b : ℝ) :
    (∑ j : Fin n, f j * (if j = p then a else if j = q then b else 0)) =
      f p * a + f q * b := by
  calc
    (∑ j : Fin n, f j * (if j = p then a else if j = q then b else 0)) =
        ∑ j : Fin n,
          ((if j = p then f j * a else 0) + (if j = q then f j * b else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hjp : j = p
          · simp [hjp, hpq]
          · by_cases hjq : j = q
            · have hqp : q ≠ p := by
                intro h
                exact hpq h.symm
              simp [hjq, hqp]
            · simp [hjp, hjq]
    _ = (∑ j : Fin n, if j = p then f j * a else 0) +
          (∑ j : Fin n, if j = q then f j * b else 0) := by
          rw [Finset.sum_add_distrib]
    _ = f p * a + f q * b := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']

/-- **Problem 8.9**, Appendix A forward witness equation:
`U_n(θ) v = s^(n-2) sqrt(1+c) u`, using the scaled witness vectors above. -/
theorem higham8_problem8_9_kahan_witness_forward
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    matMulVec n (higham8_11_kahanMatrix n c s)
        (higham8_problem8_9_kahanRightWitness n h2 c) =
      fun i =>
        s ^ (n - 2) * Real.sqrt (1 + c) *
          higham8_problem8_9_kahanLeftWitness n h2 c s i := by
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    simp [p, q, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex] at hval
    omega
  have hpval : p.val = n - 2 := rfl
  have hqval : q.val = n - 1 := rfl
  have hqpow : s ^ q.val = s ^ (n - 2) * s := by
    rw [hqval]
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hpow_nm1 : s ^ (n - 1) = s ^ (n - 2) * s := by
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hnm2_ne_nm1 : n - 2 ≠ n - 1 := by omega
  have hnm1_ne_nm2 : n - 1 ≠ n - 2 := by omega
  have hnm2_lt_nm1 : n - 2 < n - 1 := by omega
  have hnot_nm1_lt_nm2 : ¬ n - 1 < n - 2 := by omega
  have hp_lt_q : p < q := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hq_ne_p : q ≠ p := hpq.symm
  have hnot_q_lt_p : ¬ q < p := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hright :
      higham8_problem8_9_kahanRightWitness n h2 c =
        fun j =>
          if j = p then Real.sqrt (1 + c)
          else if j = q then -Real.sqrt (1 + c)
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanRightWitness, p, q]
  ext i
  unfold matMulVec
  rw [hright]
  rw [higham8_sum_two_support p q hpq]
  by_cases hip : i = p
  · subst i
    simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
      higham8_3_stressUpper, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex, p, q, hnm2_ne_nm1, hnm2_lt_nm1]
    ring_nf
  · by_cases hiq : i = q
    · subst i
      simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, higham8_problem8_9_secondSmallestIndex,
        higham8_problem8_9_lastIndex, p, q, hnm1_ne_nm2, hnot_nm1_lt_nm2]
      rw [hpow_nm1]
      ring_nf
    · have hip_lt : i.val < p.val := by
        have hi_ne_p : i.val ≠ n - 2 := by
          intro hval
          exact hip (Fin.ext (by simpa [p, hpval] using hval))
        have hi_ne_q : i.val ≠ n - 1 := by
          intro hval
          exact hiq (Fin.ext (by simpa [q, hqval] using hval))
        have hi_bound : i.val < n := i.isLt
        omega
      have hi_ne_p : i ≠ p := hip
      have hi_ne_q : i ≠ q := hiq
      have hi_lt_q : i < q := by
        rw [Fin.lt_def]
        rw [hqval]
        omega
      simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, p, q, hi_ne_p, hi_ne_q, hip_lt, hi_lt_q]

/-- **Problem 8.9**, Appendix A transpose witness equation:
`U_n(θ)^T u = s^(n-2) sqrt(1+c) v`, using the scaled witness vectors above. -/
theorem higham8_problem8_9_kahan_witness_transpose
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    matMulVec n (matTranspose (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_kahanLeftWitness n h2 c s) =
      fun i =>
        s ^ (n - 2) * Real.sqrt (1 + c) *
          higham8_problem8_9_kahanRightWitness n h2 c i := by
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    simp [p, q, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex] at hval
    omega
  have hpval : p.val = n - 2 := rfl
  have hqval : q.val = n - 1 := rfl
  have hqpow : s ^ q.val = s ^ (n - 2) * s := by
    rw [hqval]
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hpow_nm1 : s ^ (n - 1) = s ^ (n - 2) * s := by
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hnm2_ne_nm1 : n - 2 ≠ n - 1 := by omega
  have hnm1_ne_nm2 : n - 1 ≠ n - 2 := by omega
  have hnm2_lt_nm1 : n - 2 < n - 1 := by omega
  have hnot_nm1_lt_nm2 : ¬ n - 1 < n - 2 := by omega
  have hp_lt_q : p < q := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hq_ne_p : q ≠ p := hpq.symm
  have hnot_q_lt_p : ¬ q < p := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hleft :
      higham8_problem8_9_kahanLeftWitness n h2 c s =
        fun j =>
          if j = p then 1 + c
          else if j = q then -s
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanLeftWitness, p, q]
  have hright :
      higham8_problem8_9_kahanRightWitness n h2 c =
        fun j =>
          if j = p then Real.sqrt (1 + c)
          else if j = q then -Real.sqrt (1 + c)
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanRightWitness, p, q]
  have hone_c_nonneg : 0 ≤ 1 + c := by linarith
  have hsqrt_sq : Real.sqrt (1 + c) * Real.sqrt (1 + c) = 1 + c := by
    simpa [sq] using Real.sq_sqrt hone_c_nonneg
  have hsqrt_prod :
      s ^ (n - 2) * Real.sqrt (1 + c) * Real.sqrt (1 + c) =
        s ^ (n - 2) * (1 + c) := by
    rw [mul_assoc, hsqrt_sq]
  ext i
  unfold matMulVec
  rw [hleft]
  rw [higham8_sum_two_support p q hpq]
  by_cases hip : i = p
  · subst i
    simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
      higham8_3_stressUpper, matTranspose, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex, p, q, hnm1_ne_nm2, hnot_nm1_lt_nm2]
    rw [hsqrt_prod]
  · by_cases hiq : i = q
    · subst i
      simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, matTranspose, higham8_problem8_9_secondSmallestIndex,
        higham8_problem8_9_lastIndex, p, q, hnm2_ne_nm1, hnm1_ne_nm2,
        hnm2_lt_nm1]
      rw [hpow_nm1, hsqrt_prod]
      have hsum : c * (1 + c) + s * s = 1 + c := by
        nlinarith [hcs]
      calc
        -(s ^ (n - 2) * c * (1 + c)) + -(s ^ (n - 2) * s * s)
            = -s ^ (n - 2) * (c * (1 + c) + s * s) := by ring
        _ = -s ^ (n - 2) * (1 + c) := by rw [hsum]
        _ = -(s ^ (n - 2) * (1 + c)) := by ring
    · have hip_lt : i.val < p.val := by
        have hi_ne_p : i.val ≠ n - 2 := by
          intro hval
          exact hip (Fin.ext (by simpa [p, hpval] using hval))
        have hi_ne_q : i.val ≠ n - 1 := by
          intro hval
          exact hiq (Fin.ext (by simpa [q, hqval] using hval))
        have hi_bound : i.val < n := i.isLt
        omega
      have hp_ne_i : p ≠ i := by exact fun h => hip h.symm
      have hq_ne_i : q ≠ i := by exact fun h => hiq h.symm
      have hnot_p_lt_i : ¬ p < i := by
        rw [Fin.lt_def]
        omega
      have hnot_q_lt_i : ¬ q < i := by
        rw [Fin.lt_def]
        rw [hqval]
        omega
      simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, matTranspose, p, q, hip, hiq, hp_ne_i, hq_ne_i,
        hnot_p_lt_i, hnot_q_lt_i]

private theorem higham8_realRectToCMatrix_euclideanLin_realVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x) =
      realVecToEuclidean (rectMatMulVec A x) := by
  apply WithLp.ofLp_injective
  ext i
  simp [realRectToCMatrix_euclideanLin_ofLp, realVecToEuclidean,
    complexMatrixVecMul, realRectToCMatrix, rectMatMulVec]

private theorem higham8_realRectToCMatrix_euclideanLin_realVec_square {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x) =
      realVecToEuclidean (matMulVec n A x) := by
  simpa [matMulVec, rectMatMulVec] using
    higham8_realRectToCMatrix_euclideanLin_realVec A x

/-- **Problem 8.9**, Gram-eigenpair certificate for the Appendix A Kahan
witness.  This proves that the explicit candidate has squared singular value
`(s^(n-2))^2 (1+c)`; the remaining source step is to place this eigenvalue at
the ordered index `n-2`. -/
theorem higham8_problem8_9_kahan_gram_witness
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    complexMatrixGramLin (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c)) =
      (((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ) •
        realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c) := by
  let A : Fin n → Fin n → ℝ := higham8_11_kahanMatrix n c s
  let x : Fin n → ℝ := higham8_problem8_9_kahanRightWitness n h2 c
  let y : Fin n → ℝ := higham8_problem8_9_kahanLeftWitness n h2 c s
  let σ : ℝ := s ^ (n - 2) * Real.sqrt (1 + c)
  have hforward : matMulVec n A x = fun i => σ * y i := by
    simpa [A, x, y, σ] using
      higham8_problem8_9_kahan_witness_forward n h2 c s
  have htranspose : matMulVec n (matTranspose A) y = fun i => σ * x i := by
    simpa [A, x, y, σ] using
      higham8_problem8_9_kahan_witness_transpose n h2 c s hc hcs
  have hscale :
      matMulVec n (matTranspose A) (fun j => σ * y j) =
        fun i => σ * matMulVec n (matTranspose A) y i := by
    ext i
    unfold matMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreal :
      matMulVec n (matMul n (matTranspose A) A) x =
        fun i => σ ^ 2 * x i := by
    ext i
    calc
      matMulVec n (matMul n (matTranspose A) A) x i =
          matMulVec n (matTranspose A) (matMulVec n A x) i :=
            matMulVec_matMul n (matTranspose A) A x i
      _ = matMulVec n (matTranspose A) (fun j => σ * y j) i := by
            rw [hforward]
      _ = σ * matMulVec n (matTranspose A) y i := by
            rw [hscale]
      _ = σ * (σ * x i) := by
            rw [htranspose]
      _ = σ ^ 2 * x i := by ring
  have hsigma_sq : σ ^ 2 = (s ^ (n - 2)) ^ 2 * (1 + c) := by
    dsimp [σ]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  rw [← complexMatrixEuclideanLin_adjoint_mul_self (realRectToCMatrix A)]
  rw [← realRectToCMatrix_matTranspose A]
  rw [← realRectToCMatrix_matMul]
  rw [higham8_realRectToCMatrix_euclideanLin_realVec_square]
  rw [hreal]
  apply WithLp.ofLp_injective
  ext i
  change ((σ ^ 2 * x i : ℝ) : ℂ) =
    (((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ) * (x i : ℂ)
  rw [hsigma_sq]
  norm_num [Complex.ofReal_mul]

/-- **Problem 8.9** support: the Appendix A witness gives an actual Gram
eigenvalue, not only a formal action equation.  The remaining source step is
the ordered placement at index `n - 2`. -/
theorem higham8_problem8_9_kahan_candidate_hasGramEigenvalue
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    Module.End.HasEigenvalue
      (complexMatrixGramLin (realRectToCMatrix (higham8_11_kahanMatrix n c s)))
      ((((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ)) := by
  let v := realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c)
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    simpa [v] using higham8_problem8_9_kahan_gram_witness n h2 c s hc hcs
  · exact higham8_problem8_9_kahanRightWitness_euclidean_ne_zero n h2 c hc

/-- **Problem 8.9** support: the Appendix A candidate occurs somewhere in the
repository's sorted Gram-eigenvalue list.  Problem 8.9 remains open precisely
because this theorem does not identify the occurrence with index `n - 2`. -/
theorem higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ i : Fin n,
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s)) i =
        (s ^ (n - 2)) ^ 2 * (1 + c) := by
  obtain ⟨i, hi⟩ :=
    (complexMatrixGramLin_isSymmetric
      (realRectToCMatrix (higham8_11_kahanMatrix n c s))).exists_eigenvalues_eq
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))
      (higham8_problem8_9_kahan_candidate_hasGramEigenvalue n h2 c s hc hcs)
  exact ⟨i, Complex.ofReal_injective (by
    simpa [complexMatrixGramEigenvalues] using hi)⟩

private theorem higham8_complexMatrixRank_rankOne_standard_le_one
    {m n : ℕ} (i0 : Fin m) (y : CVec n) :
    complexMatrixRank (complexMatrixRankOne (standardBasisCVec i0) y) ≤ 1 := by
  unfold complexMatrixRank
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan_le :
      Submodule.span ℂ
          (Set.range
            (Matrix.col
              (complexMatrixRankOne (standardBasisCVec i0) y :
                Matrix (Fin m) (Fin n) ℂ))) ≤
        ℂ ∙ standardBasisCVec i0 := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    have hcol :
        Matrix.col
            (complexMatrixRankOne (standardBasisCVec i0) y : Matrix (Fin m) (Fin n) ℂ) j =
          y j • standardBasisCVec i0 := by
      ext i
      simp [complexMatrixRankOne, mul_comm]
    rw [hcol]
    exact Submodule.smul_mem (ℂ ∙ standardBasisCVec i0) (y j)
      (Submodule.mem_span_singleton_self (standardBasisCVec i0))
  calc
    Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range
            (Matrix.col
              (complexMatrixRankOne (standardBasisCVec i0) y :
                Matrix (Fin m) (Fin n) ℂ)))) ≤
        Module.finrank ℂ (ℂ ∙ standardBasisCVec i0) :=
          Submodule.finrank_mono hspan_le
    _ = 1 := finrank_span_singleton (standardBasisCVec_ne_zero i0)

private theorem higham8_problem8_9_kahan_zero_eq_rankOne
    (n : ℕ) (hn : 0 < n) :
    realRectToCMatrix (higham8_11_kahanMatrix n 1 0) =
      complexMatrixRankOne (standardBasisCVec (⟨0, hn⟩ : Fin n))
        (fun j => realRectToCMatrix (higham8_11_kahanMatrix n 1 0)
          (⟨0, hn⟩ : Fin n) j) := by
  let z : Fin n := ⟨0, hn⟩
  ext i j
  by_cases hi : i = z
  · subst i
    simp [complexMatrixRankOne, standardBasisCVec, z]
  · have hi' : i ≠ (⟨0, hn⟩ : Fin n) := by simpa [z] using hi
    have hi_pos : 0 < i.val := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hzero
        exact hi' (Fin.ext (by simpa using hzero))
      omega
    have hpow : (0 : ℝ) ^ i.val = 0 := zero_pow (Nat.ne_of_gt hi_pos)
    simp [realRectToCMatrix, higham8_11_kahanMatrix, complexMatrixRankOne,
      standardBasisCVec, hi', hpow]

private theorem higham8_problem8_9_kahan_zero_rank_le_one
    (n : ℕ) (hn : 0 < n) :
    complexMatrixRank (realRectToCMatrix (higham8_11_kahanMatrix n 1 0)) ≤ 1 := by
  rw [higham8_problem8_9_kahan_zero_eq_rankOne n hn]
  exact higham8_complexMatrixRank_rankOne_standard_le_one (⟨0, hn⟩ : Fin n)
    (fun j => realRectToCMatrix (higham8_11_kahanMatrix n 1 0) (⟨0, hn⟩ : Fin n) j)

private theorem higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one
    {m n : ℕ} (A : CMatrix m n) (i : Fin n)
    (hi : 1 ≤ i.val) (hrank : complexMatrixRank A ≤ 1) :
    complexMatrixGramEigenvalues A i = 0 := by
  classical
  by_contra hne
  let z : Fin n := ⟨0, by omega⟩
  have hz_ne_i : z ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    simp [z] at hval
    omega
  have hpos_i : 0 < complexMatrixGramEigenvalues A i := by
    exact lt_of_le_of_ne (complexMatrixGramEigenvalues_nonneg A i) (by
      intro hzero
      exact hne hzero.symm)
  have hle : complexMatrixGramEigenvalues A i ≤ complexMatrixGramEigenvalues A z := by
    exact (complexMatrixGramEigenvalues_antitone A) (by
      rw [Fin.le_iff_val_le_val]
      simp [z])
  have hz_ne_zero : complexMatrixGramEigenvalues A z ≠ 0 := by
    have hz_pos : 0 < complexMatrixGramEigenvalues A z := lt_of_lt_of_le hpos_i hle
    exact ne_of_gt hz_pos
  have hcard : Fintype.card {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} ≤ 1 := by
    have hcount := complexMatrixRank_eq_card_nonzero_gramEigenvalues (A := A)
    omega
  have hsub : Subsingleton {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} :=
    Fintype.card_le_one_iff_subsingleton.mp hcard
  let zi : {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} := ⟨z, hz_ne_zero⟩
  let ii : {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} := ⟨i, hne⟩
  have hzi : zi = ii := Subsingleton.elim zi ii
  exact hz_ne_i (Subtype.ext_iff.mp hzi)

private theorem higham8_complexMatrixGramEigenvalues_top_eq_of_rank_le_one_of_mem_nonzero
    {m n : ℕ} (A : CMatrix m n) (hn : 0 < n) {lam : ℝ}
    (hlam : lam ≠ 0) (hrank : complexMatrixRank A ≤ 1)
    (hmem : ∃ i : Fin n, complexMatrixGramEigenvalues A i = lam) :
    complexMatrixGramEigenvalues A (⟨0, hn⟩ : Fin n) = lam := by
  rcases hmem with ⟨i, hi⟩
  by_cases hiz : i = (⟨0, hn⟩ : Fin n)
  · simpa [hiz] using hi
  · have hi_pos : 1 ≤ i.val := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hzero
        exact hiz (Fin.ext (by simpa using hzero))
      omega
    have hzero := higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one A i hi_pos hrank
    exact False.elim (hlam (by simpa [hi] using hzero))

theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_three_le
    (n : ℕ) (h3 : 3 ≤ n) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n 1 0))
        (higham8_problem8_9_secondSmallestIndex n (by omega)) =
      (0 ^ (n - 2)) ^ 2 * (1 + (1 : ℝ)) := by
  let p := higham8_problem8_9_secondSmallestIndex n (by omega : 2 ≤ n)
  have hp_pos : 1 ≤ p.val := by
    simp [p, higham8_problem8_9_secondSmallestIndex]
    omega
  have hzero :
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n 1 0)) p = 0 :=
    higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one _ p hp_pos
      (higham8_problem8_9_kahan_zero_rank_le_one n (by omega))
  have hpow : (0 : ℝ) ^ (n - 2) = 0 :=
    zero_pow (by omega : n - 2 ≠ 0)
  rw [hzero, hpow]
  ring

theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_two :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix 2 1 0))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
  let A : CMatrix 2 2 := realRectToCMatrix (higham8_11_kahanMatrix 2 1 0)
  have hmem :
      ∃ i : Fin 2,
        complexMatrixGramEigenvalues A i =
          (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
    simpa [A] using
      higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
        2 (by norm_num : 2 ≤ 2) 1 0 (by norm_num) (by norm_num)
  have htop :
      complexMatrixGramEigenvalues A (⟨0, by norm_num⟩ : Fin 2) =
        (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
    apply higham8_complexMatrixGramEigenvalues_top_eq_of_rank_le_one_of_mem_nonzero A
      (by norm_num)
    · norm_num
    · simpa [A] using higham8_problem8_9_kahan_zero_rank_le_one 2 (by norm_num)
    · exact hmem
  have hp :
      higham8_problem8_9_secondSmallestIndex 2 (by norm_num : 2 ≤ 2) =
        (⟨0, by norm_num⟩ : Fin 2) := by
    ext
    simp [higham8_problem8_9_secondSmallestIndex]
  simpa [A, hp] using htop

theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_zero
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_zero : s = 0) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  subst s
  have hc_sq : c ^ 2 = 1 := by nlinarith
  have hc_one : c = 1 := by
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  subst c
  by_cases hn2 : n = 2
  · subst n
    simpa using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_two
  · have h3 : 3 ≤ n := by omega
    simpa using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_three_le n h3

theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_zero : s = 0) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc
  · rw [hs_zero]
  · exact
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_zero
        n h2 c s hc hcs hs_zero

/-- **Problem 8.9** support: in the source branch `0 < s < 1`, the already
proved smallest-slot exclusion and witness eigenvalue prove the easy ordered
half: the second-smallest Gram eigenvalue is no larger than the Appendix A
candidate.  The missing half is the interlacing lower bound. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  let A : CMatrix n n := realRectToCMatrix (higham8_11_kahanMatrix n c s)
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  let σ := higham8_problem8_9_kahanSecondSmallestValue n c s
  let lam : ℝ := (s ^ (n - 2)) ^ 2 * (1 + c)
  have hσ_nonneg : 0 ≤ σ := by
    exact mul_nonneg (pow_nonneg (le_of_lt hs_pos) _) (Real.sqrt_nonneg _)
  have hsmall :
      complexMatrixSingularValue A q < σ := by
    simpa [A, q, σ] using
      higham8_problem8_9_kahan_smallestSingularValue_lt_candidate
        n h2 c s hc hs_pos hs_lt
  have hlast_lt : complexMatrixGramEigenvalues A q < lam := by
    have hsq :
        complexMatrixSingularValue A q ^ 2 < σ ^ 2 :=
      (sq_lt_sq₀ (complexMatrixSingularValue_nonneg A q) hσ_nonneg).2 hsmall
    have hσ_sq : σ ^ 2 = lam := by
      simp [σ, lam, higham8_problem8_9_kahanSecondSmallestValue, mul_pow,
        Real.sq_sqrt (by linarith : 0 ≤ 1 + c)]
    rw [complexMatrixSingularValue_sq, hσ_sq] at hsq
    exact hsq
  obtain ⟨i, hi⟩ :=
    higham8_problem8_9_kahan_candidate_mem_gramEigenvalues n h2 c s hc hcs
  have hi_ne_q : i ≠ q := by
    intro hiq
    have hqeq : complexMatrixGramEigenvalues A q = lam := by
      simpa [A, q, lam, hiq] using hi
    exact (ne_of_lt hlast_lt) hqeq
  have hi_le_p : i ≤ p := by
    rw [Fin.le_iff_val_le_val]
    have hi_val_ne : i.val ≠ n - 1 := by
      intro hv
      apply hi_ne_q
      exact Fin.ext (by
        simpa [q, higham8_problem8_9_lastIndex] using hv)
    have hi_bound : i.val < n := i.isLt
    simp [p, higham8_problem8_9_secondSmallestIndex]
    omega
  have hp_le_hi : complexMatrixGramEigenvalues A p ≤ complexMatrixGramEigenvalues A i :=
    (complexMatrixGramEigenvalues_antitone A) hi_le_p
  simpa [A, p, lam, hi] using hp_le_hi

/-- **Problem 8.9** support: the exact ordered Gram-eigenvalue statement follows
from the sole missing source-side lower bound.  The lower bound is the
interlacing/min-max step from Appendix A. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hlower :
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  exact le_antisymm
    (higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
      n h2 c s hc hcs hs_pos hs_lt)
    hlower

/-- **Problem 8.9** support: once the interlacing lower bound places the
candidate at the ordered Gram slot `n - 2`, the displayed singular-value
formula follows from the local SVD/Gram reduction. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hlower :
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc (le_of_lt hs_pos)
  exact
    higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound
      n h2 c s hc hcs hs_pos hs_lt hlower

/-- **Problem 8.9** base case: for the `2 × 2` Kahan matrix, the target
`second-smallest` slot is the top sorted Gram eigenvalue, so candidate
membership and antitonicity give the missing lower bound without interlacing. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
    (c s : ℝ) (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix 2 c s))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      (s ^ (2 - 2)) ^ 2 * (1 + c) := by
  let A : CMatrix 2 2 := realRectToCMatrix (higham8_11_kahanMatrix 2 c s)
  let p := higham8_problem8_9_secondSmallestIndex 2 (by norm_num : 2 ≤ 2)
  let lam : ℝ := (s ^ (2 - 2)) ^ 2 * (1 + c)
  have hp_top : p = (⟨0, by norm_num⟩ : Fin 2) := by
    ext
    simp [p, higham8_problem8_9_secondSmallestIndex]
  have hupper : complexMatrixGramEigenvalues A p ≤ lam := by
    simpa [A, p, lam] using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
        2 (by norm_num : 2 ≤ 2) c s hc hcs hs_pos hs_lt
  have hlower : lam ≤ complexMatrixGramEigenvalues A p := by
    obtain ⟨i, hi⟩ :=
      higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
        2 (by norm_num : 2 ≤ 2) c s hc hcs
    have hp_le_i : p ≤ i := by
      rw [hp_top]
      exact Fin.zero_le i
    have hi_le_top : complexMatrixGramEigenvalues A i ≤ complexMatrixGramEigenvalues A p :=
      (complexMatrixGramEigenvalues_antitone A) hp_le_i
    simpa [A, lam, hi] using hi_le_top
  exact le_antisymm hupper hlower

/-- **Problem 8.9** base case: the displayed second-smallest singular value is
closed for `n = 2` in the source branch `0 < s < 1`. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_two
    (c s : ℝ) (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix 2 c s))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      higham8_problem8_9_kahanSecondSmallestValue 2 c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    2 (by norm_num : 2 ≤ 2) c s hc (le_of_lt hs_pos)
  exact higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
    c s hc hcs hs_pos hs_lt

/-- **Problem 8.9** induction reduction: if the one-step Cauchy-interlacing
consequence holds for the leading Kahan Gram blocks, then the displayed
interior Gram eigenvalue formula follows for every size.

The required interlacing consequence is the exact source induction step: the
previous-size second-smallest Gram eigenvalue is no larger than the current
third-smallest Gram eigenvalue.  The remaining project-level spectral blocker
is proving that hypothesis from a reusable interlacing/min-max theorem. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ (hk2 : 2 ≤ k),
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix k c s))
          (higham8_problem8_9_secondSmallestIndex k hk2) =
        (s ^ (k - 2)) ^ 2 * (1 + c)
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk2
        by_cases hk_two : k = 2
        · subst k
          exact
            higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
              c s hc hcs hs_pos hs_lt
        · have hk3 : 3 ≤ k := by omega
          let A : CMatrix k k := realRectToCMatrix (higham8_11_kahanMatrix k c s)
          let p := higham8_problem8_9_secondSmallestIndex k hk2
          let q := higham8_problem8_9_lastIndex k (by omega : 0 < k)
          let r := higham8_problem8_9_thirdSmallestIndex k hk3
          let lam : ℝ := (s ^ (k - 2)) ^ 2 * (1 + c)
          let lamPrev : ℝ := (s ^ ((k - 1) - 2)) ^ 2 * (1 + c)
          have hprev2 : 2 ≤ k - 1 := by omega
          have hprev :
              complexMatrixGramEigenvalues
                  (realRectToCMatrix (higham8_11_kahanMatrix (k - 1) c s))
                  (higham8_problem8_9_secondSmallestIndex (k - 1) hprev2) =
                lamPrev := by
            simpa [P, lamPrev] using ih (k - 1) (by omega) hprev2
          have hthird_ge_prev : lamPrev ≤ complexMatrixGramEigenvalues A r := by
            calc
              lamPrev =
                  complexMatrixGramEigenvalues
                    (realRectToCMatrix (higham8_11_kahanMatrix (k - 1) c s))
                    (higham8_problem8_9_secondSmallestIndex (k - 1) (by omega)) := by
                      simpa [lamPrev] using hprev.symm
              _ ≤ complexMatrixGramEigenvalues A r := by
                      simpa [A, r] using hinterlace k hk3
          have hs_sq_lt_one : s ^ 2 < 1 := by
            nlinarith [mul_lt_mul_of_pos_right hs_lt hs_pos]
          have hprev_pos : 0 < lamPrev := by
            have hpow_pos : 0 < s ^ ((k - 1) - 2) := pow_pos hs_pos _
            have hc_pos : 0 < 1 + c := by linarith
            exact mul_pos (sq_pos_of_pos hpow_pos) hc_pos
          have hlam_lt_prev : lam < lamPrev := by
            have hkidx : k - 2 = (k - 1) - 2 + 1 := by omega
            have hrewrite :
                lam = s ^ 2 * lamPrev := by
              simp [lam, lamPrev, hkidx, pow_succ]
              ring
            rw [hrewrite]
            simpa using mul_lt_mul_of_pos_right hs_sq_lt_one hprev_pos
          have hthird_gt_lam : lam < complexMatrixGramEigenvalues A r :=
            hlam_lt_prev.trans_le hthird_ge_prev
          obtain ⟨i, hi⟩ :=
            higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
              k hk2 c s hc hcs
          have hi_not_le_r : ¬ i ≤ r := by
            intro hir
            have hr_le_i :
                complexMatrixGramEigenvalues A r ≤ complexMatrixGramEigenvalues A i :=
              complexMatrixGramEigenvalues_antitone A hir
            have hr_le_lam : complexMatrixGramEigenvalues A r ≤ lam := by
              simpa [A, lam, hi] using hr_le_i
            exact (not_lt_of_ge hr_le_lam) hthird_gt_lam
          have hi_val_gt_r : r.val < i.val := by
            by_contra hle
            exact hi_not_le_r (Fin.le_iff_val_le_val.2 (by omega))
          have hi_ge_p_val : p.val ≤ i.val := by
            simp [p, higham8_problem8_9_secondSmallestIndex]
            simp [r, higham8_problem8_9_thirdSmallestIndex] at hi_val_gt_r
            omega
          have hlast_lt :
              complexMatrixGramEigenvalues A q < lam := by
            simpa [A, q, lam] using
              higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate
                k hk2 c s hc hs_pos hs_lt
          have hi_ne_q : i ≠ q := by
            intro hiq
            have hqeq : complexMatrixGramEigenvalues A q = lam := by
              simpa [A, q, lam, hiq] using hi
            exact (ne_of_lt hlast_lt) hqeq
          have hi_eq_p : i = p := by
            apply Fin.ext
            have hi_ne_last_val : i.val ≠ k - 1 := by
              intro hv
              apply hi_ne_q
              exact Fin.ext (by
                simpa [q, higham8_problem8_9_lastIndex] using hv)
            have hi_lt_last : i.val < k - 1 := by
              have hi_lt_k : i.val < k := i.isLt
              omega
            simp [p, higham8_problem8_9_secondSmallestIndex] at hi_ge_p_val ⊢
            omega
          simpa [A, p, lam, hi_eq_p] using hi
  exact hmain n h2

/-- **Problem 8.9** induction reduction, singular-value form: the source
interior formula follows from the exact one-step Cauchy-interlacing consequence
for the leading Kahan Gram blocks. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc (le_of_lt hs_pos)
  exact
    higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
      n h2 c s hc hcs hs_pos hs_lt hinterlace

theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hlower : 3 ≤ n → 0 < s → s < 1 →
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  by_cases hs_zero : s = 0
  · exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero
      n h2 c s hc hcs hs_zero
  · by_cases hs_one : s = 1
    · exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one
        n h2 c s hc hcs hs_one
    · have hs_pos : 0 < s := lt_of_le_of_ne hs (by
        intro hzero
        exact hs_zero hzero.symm)
      have hs_lt : s < 1 := by
        have hs_sq_le : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
        have hs_le : s ≤ 1 := by
          simpa using Real.le_sqrt_of_sq_le hs_sq_le
        exact lt_of_le_of_ne hs_le hs_one
      by_cases hn2 : n = 2
      · subst n
        exact higham8_problem8_9_kahan_secondSmallestSingularValue_two
          c s hc hcs hs_pos hs_lt
      · have h3 : 3 ≤ n := by omega
        exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound
          n h2 c s hc hcs hs_pos hs_lt (hlower h3 hs_pos hs_lt)

/-- **Problem 8.9** all-cases reduction to the Kahan Gram interlacing step.
Once the leading-principal-block Cauchy interlacing consequence is available,
this theorem closes the displayed second-smallest singular-value formula without
any separate edge-case assumptions. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply
    higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound
      n h2 c s hc hs hcs
  intro h3 hs_pos hs_lt
  exact le_of_eq
    (higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
      n h2 c s hc hcs hs_pos hs_lt hinterlace).symm

/-- **Problem 8.9**: for Kahan's matrix in (8.11), the second-smallest
singular value is `s^(n-2) * sqrt (1+c)` in the repository's descending
singular-value order. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  exact
    higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing
      n h2 c s hc hs hcs
      (higham8_problem8_9_kahanGram_interlacing c s)

/-- **Problem 8.2**, Appendix A witness `T(λ)`. -/
noncomputable def higham8_2_ratioWitness (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 / lam
    else if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 0 ∧ j.val = 2 then 1
    else if i.val = 1 ∧ j.val = 1 then 1 / lam
    else if i.val = 1 ∧ j.val = 2 then 1 / lam
    else if i.val = 2 ∧ j.val = 2 then 1 / lam ^ 2
    else 0

/-- **Problem 8.2**, explicit inverse for the Appendix A witness `T(λ)`. -/
noncomputable def higham8_2_ratioWitnessInv (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then lam
    else if i.val = 0 ∧ j.val = 1 then -(lam ^ 2)
    else if i.val = 1 ∧ j.val = 1 then lam
    else if i.val = 1 ∧ j.val = 2 then -(lam ^ 2)
    else if i.val = 2 ∧ j.val = 2 then lam ^ 2
    else 0

/-- **Problem 8.2**, the explicit comparison matrix `M(T(λ))`. -/
noncomputable def higham8_2_ratioWitnessComparison (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 / lam
    else if i.val = 0 ∧ j.val = 1 then -1
    else if i.val = 0 ∧ j.val = 2 then -1
    else if i.val = 1 ∧ j.val = 1 then 1 / lam
    else if i.val = 1 ∧ j.val = 2 then -(1 / lam)
    else if i.val = 2 ∧ j.val = 2 then 1 / lam ^ 2
    else 0

/-- **Problem 8.2**, explicit inverse of `M(T(λ))`. -/
noncomputable def higham8_2_ratioWitnessComparisonInv (lam : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then lam
    else if i.val = 0 ∧ j.val = 1 then lam ^ 2
    else if i.val = 0 ∧ j.val = 2 then 2 * lam ^ 3
    else if i.val = 1 ∧ j.val = 1 then lam
    else if i.val = 1 ∧ j.val = 2 then lam ^ 2
    else if i.val = 2 ∧ j.val = 2 then lam ^ 2
    else 0

/-- The Appendix A witness is upper triangular. -/
lemma higham8_2_ratioWitness_upper (lam : ℝ) :
    ∀ i j : Fin 3, j.val < i.val → higham8_2_ratioWitness lam i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [higham8_2_ratioWitness] at hij ⊢

/-- The Appendix A inverse formula is a genuine two-sided inverse of `T(λ)`. -/
theorem higham8_2_ratioWitness_isInverse (lam : ℝ) (hlam : lam ≠ 0) :
    IsInverse 3 (higham8_2_ratioWitness lam) (higham8_2_ratioWitnessInv lam) := by
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham8_2_ratioWitness, higham8_2_ratioWitnessInv, hlam] <;>
    field_simp [hlam] <;> ring

/-- The comparison matrix of the Appendix A witness is the expected signed
upper-triangular matrix. -/
theorem higham8_2_ratioWitness_comparison_eq (lam : ℝ) (hlam : 0 ≤ lam) :
    comparisonMatrix 3 (higham8_2_ratioWitness lam) =
      higham8_2_ratioWitnessComparison lam := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [comparisonMatrix, higham8_2_ratioWitness, higham8_2_ratioWitnessComparison,
      abs_of_nonneg hlam]

/-- The explicit Appendix A formula is a genuine inverse of `M(T(λ))`. -/
theorem higham8_2_ratioWitnessComparisonInv_isInverse (lam : ℝ) (hlam : lam ≠ 0) :
    IsInverse 3 (higham8_2_ratioWitnessComparison lam)
      (higham8_2_ratioWitnessComparisonInv lam) := by
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparison,
      higham8_2_ratioWitnessComparisonInv, hlam] <;>
    field_simp [hlam] <;> ring

private theorem higham8_2_ratioWitnessInv_row0_abs_sum (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessInv lam 0 j| = lam + lam ^ 2 := by
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam,
    abs_of_nonneg (sq_nonneg lam)]

private theorem higham8_2_ratioWitnessComparisonInv_row0_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessComparisonInv lam 0 j| =
      lam + lam ^ 2 + 2 * lam ^ 3 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg hlam, abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]

private theorem higham8_2_ratioWitnessComparisonInv_col2_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ i : Fin 3, |higham8_2_ratioWitnessComparisonInv lam i 2| =
      2 * lam ^ 3 + 2 * lam ^ 2 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]
  ring

private theorem higham8_2_ratioWitnessInv_infNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    infNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply infNorm_le_of_row_sum_le
  · intro i
    fin_cases i
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith

private theorem higham8_2_ratioWitnessInv_oneNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    oneNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply oneNorm_le_of_col_sum_le
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith

/-- **Problem 8.2**, appendix witness in the infinity norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖∞ / ‖T(λ)⁻¹‖∞` is at least `λ`. -/
theorem higham8_2_comparisonInverseInfNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      infNorm (higham8_2_ratioWitnessComparisonInv lam) /
        infNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_row :=
    row_sum_le_infNorm (higham8_2_ratioWitnessComparisonInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_row0_abs_sum lam hlam0] at hnum_row
  have hnum : 2 * lam ^ 3 ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_infNorm_le lam hlam
  have hden_row := row_sum_le_infNorm (higham8_2_ratioWitnessInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessInv_row0_abs_sum lam hlam0] at hden_row
  have hden_pos : 0 < infNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (infNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := hmid

/-- **Problem 8.2**, appendix witness in the one norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖₁ / ‖T(λ)⁻¹‖₁` is at least `λ`. -/
theorem higham8_2_comparisonInverseOneNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
        oneNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessComparisonInv lam) (2 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_col2_abs_sum lam hlam0] at hnum_col
  have hnum : 2 * lam ^ 3 ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_oneNorm_le lam hlam
  have hden_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessInv lam) (2 : Fin 3)
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg (sq_nonneg lam)]
    at hden_col
  have hden_pos : 0 < oneNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (oneNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := hmid

/-- **Problem 8.2**: the Appendix A witness makes both the `1`- and `∞`-norm
comparison-inverse ratios arbitrarily large. -/
theorem higham8_2_comparisonInverseRatios_arbitrarily_large (R : ℝ) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      R ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
            infNorm (higham8_2_ratioWitnessInv lam) ∧
      R ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
            oneNorm (higham8_2_ratioWitnessInv lam) := by
  refine ⟨max 1 R, le_max_left _ _, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseInfNormRatio_ge_lambda (max 1 R) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseOneNormRatio_ge_lambda (max 1 R) (le_max_left _ _)

/-- **Lemma 8.6**: diagonal-dominance bound for `|U⁻¹||U|`. -/
theorem higham8_6_inv_abs_mul_bound_diagDom (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n, i.val ≤ j.val →
      ∑ k : Fin n, |U_inv i k| * |U k j| ≤ 2 ^ (j.val - i.val) :=
  inv_abs_mul_bound_diagDom n U U_inv hDD hInv

/-- **Theorem 8.7**: componentwise forward error under condition (8.5). -/
theorem higham8_7_backSub_forward_error_diagDom (fp : FPModel) (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n) :
    let x_hat := fl_backSub fp n U b
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      2 ^ (n - i.val) * gamma fp n *
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val))
            ⟨i, by simp [Finset.mem_filter]⟩ (fun j => |x_hat j|) :=
  backSub_forward_error_diagDom fp n U U_inv x b hDD hInv hTx hn

/-- **Equation (8.6)**: lower-triangular analogue of condition (8.5). -/
def higham8_6_diagDominantLower (n : ℕ) (L : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i.val < j.val → L i j = 0) ∧
  (∀ i : Fin n, L i i ≠ 0) ∧
  (∀ i j : Fin n, j.val < i.val → |L i j| ≤ |L i i|)

/-- Source condition preceding **Lemma 8.8**, as printed in the PDF:
`|u_ii| ≤ sum_{j=i+1}^n |u_ij|` for rows `i = 1:n-1`, together with upper
triangular shape.  The inequality direction is intentionally the source text's
direction. -/
def higham8_rowDominantUpperSource (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  ∀ i : Fin n, i.val + 1 < n →
    |U i i| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j|

/-- Corrected source-facing condition for **Lemma 8.8**: `U` is upper
triangular with nonzero diagonal and the strict-upper absolute row sum is
bounded by the diagonal magnitude in each row. -/
def higham8_8_rowDiagDominantUpper (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val < i.val → U i j = 0) ∧
  (∀ i : Fin n, U i i ≠ 0) ∧
  (∀ i : Fin n,
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j| ≤ |U i i|)

/-- **Lemma 8.8**, corrected theorem surface after the source audit.

If an upper-triangular matrix has nonzero diagonal and each strict-upper row
sum is bounded by the diagonal magnitude, then its Skeel condition number is
at most `2n - 1`. -/
theorem higham8_8_rowDiagDominantUpper_condSkeel_bound (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 := by
  rcases hRD with ⟨hUT, hDiag, hRow⟩
  rcases hInv with ⟨hLInv, hRInv⟩
  have hInv_ut := inv_upper_tri n U U_inv hUT hDiag hLInv
  let V : Fin n → Fin n → ℝ := fun a b => U a b / U a a
  let V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab
    simp [V, hUT a b hab]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a
    simp [V, hDiag a]
  have hV_row : ∀ a : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j| ≤ 1 := by
    intro a
    calc
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j|
          = (1 / |U a a|) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |U a j| := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp [V, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / |U a a|) * |U a a| := by
            exact mul_le_mul_of_nonneg_left (hRow a) (one_div_nonneg.mpr (abs_nonneg _))
      _ = 1 := by
            rw [one_div, inv_mul_cancel₀]
            exact abs_ne_zero.mpr (hDiag a)
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab
    simp [V_inv, hInv_ut a b hab]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a
    simp [V_inv, inv_diag_entry n U U_inv hUT hDiag hLInv hInv_ut a, hDiag a]
  have hVRInv : IsRightInverse n V V_inv := by
    intro a b
    unfold V V_inv
    have hsimp :
        ∑ k : Fin n, (U a k / U a a) * (U_inv k b * U b b) =
          (U b b / U a a) * ∑ k : Fin n, U a k * U_inv k b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [hDiag a]
    rw [hsimp, hRInv a b]
    by_cases hab : a = b
    · subst hab
      simp [hDiag a]
    · simp [hab]
  have hVinv_le_one :=
    unitUpperTri_inv_entry_le_one_of_row_sum_le_one
      n V V_inv hVT hV_unit hV_row hVRInv hVinv_ut hVinv_diag
  let rowMass : Fin n → ℝ := fun j => ∑ k : Fin n, |U j k|
  have hrow_le_two_diag : ∀ j : Fin n, rowMass j ≤ 2 * |U j j| := by
    intro j
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest_eq :
        ∑ k ∈ Finset.univ.erase j, |U j k| =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val < k.val), |U j k| := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬ j.val < k.val := by
          intro hlt
          exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        have hlt : k.val < j.val := by
          by_contra hge
          push_neg at hge
          exact hk.1 (Fin.ext (by omega))
        rw [hUT j k hlt, abs_zero]
    rw [hrest_eq]
    linarith [hRow j]
  let last : Fin n := ⟨n - 1, by omega⟩
  have hrow_last : rowMass last = |U last last| := by
    unfold rowMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
    suffices hrest : ∑ k ∈ Finset.univ.erase last, |U last k| = 0 by
      linarith
    apply Finset.sum_eq_zero
    intro k hk
    have hk_ne : k ≠ last := Finset.ne_of_mem_erase hk
    have hlt : k.val < last.val := by
      have hk_last : k.val ≠ n - 1 := by
        intro hk_eq
        apply hk_ne
        exact Fin.ext (by simpa [last] using hk_eq)
      show k.val < n - 1
      omega
    rw [hUT last k hlt, abs_zero]
  have hsum_upper :
      ∀ i : Fin n,
      ∑ j : Fin n, |U_inv i j| * rowMass j =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val),
          |U_inv i j| * rowMass j := by
    intro i
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    rw [hInv_ut i j hj, abs_zero, zero_mul]
  unfold condSkeel
  apply Finset.sup'_le
  intro i _
  change ∑ j : Fin n, |U_inv i j| * rowMass j ≤ 2 * (n : ℝ) - 1
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val ≤ j.val)
  have hlast_mem : last ∈ S := by
    simp [S, last]
    show i.val ≤ n - 1
    omega
  have hlast_term : |U_inv i last| * rowMass last ≤ 1 := by
    rw [hrow_last]
    calc
      |U_inv i last| * |U last last| = |V_inv i last| := by
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 1 := hVinv_le_one i last (by
        show i.val ≤ n - 1
        omega)
  have hrest_le :
      ∑ j ∈ S.erase last, |U_inv i j| * rowMass j ≤
        ∑ j ∈ S.erase last, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
    have hij : i.val ≤ j.val := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      exact hjS
    calc
      |U_inv i j| * rowMass j ≤ |U_inv i j| * (2 * |U j j|) := by
        exact mul_le_mul_of_nonneg_left (hrow_le_two_diag j) (abs_nonneg _)
      _ = 2 * |V_inv i j| := by
        ring_nf
        simp [V_inv, abs_mul, mul_comm]
      _ ≤ 2 := by
        have hle : |V_inv i j| ≤ 1 := hVinv_le_one i j hij
        nlinarith
  have hrest_subset :
      ∑ j ∈ S.erase last, (2 : ℝ) ≤ ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro j hj
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩)
      (by
        intro j _ _
        positivity)
  calc
    ∑ j : Fin n, |U_inv i j| * rowMass j
        = ∑ j ∈ S, |U_inv i j| * rowMass j := by
            simpa [S] using hsum_upper i
    _ = |U_inv i last| * rowMass last +
          ∑ j ∈ S.erase last, |U_inv i j| * rowMass j := by
            rw [← Finset.add_sum_erase _ _ hlast_mem]
    _ ≤ 1 + ∑ j ∈ S.erase last, (2 : ℝ) := by
          exact add_le_add hlast_term hrest_le
    _ ≤ 1 + ∑ j ∈ Finset.univ.erase last, (2 : ℝ) := by
          simpa [add_comm] using add_le_add_left hrest_subset 1
    _ = 2 * (n : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ last),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          ring

/-- The absolute value of the comparison matrix agrees entrywise with `|T|`. -/
private lemma comparisonMatrix_abs_apply (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| = |T i j| := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix]
  · simp [comparisonMatrix, hij]

/-- Entrywise decomposition of `|M(T)|` as `2 diag(|t_ii|) - M(T)`. -/
private lemma comparisonMatrix_abs_eq_two_diag_sub (n : ℕ) (T : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    |comparisonMatrix n T i j| =
      2 * diagMatrix (fun k : Fin n => |T k k|) i j - comparisonMatrix n T i j := by
  by_cases hij : i = j
  · subst hij
    simp [comparisonMatrix, diagMatrix]
    ring
  · simp [comparisonMatrix, diagMatrix, hij]

/-- **Lemma 8.9**, explicit image vector
`(2 M(T)⁻¹ diag(|t_ii|) - I)|x|`. -/
noncomputable def higham8_9_comparisonImage (n : ℕ)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * ∑ j : Fin n, M_inv i j * |T j j| * |x j| - |x i|

/-- **Lemma 8.9**, equality part for the comparison matrix:
`cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_comparisonMatrix_condAtSolution_eq (n : ℕ) (hn : 0 < n)
    (T M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j)
    (hM_left : IsLeftInverse n (comparisonMatrix n T) M_inv) :
    ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x =
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have hdiagMul :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k =
          M_inv i k * |T k k| := by
    intro i k
    simpa [matMul] using
      matMul_diagMatrix_right M_inv (fun l : Fin n => |T l l|) i k
  have hleftEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k = idMatrix n i k := by
    intro i k
    simpa [idMatrix] using hM_left i k
  have hcomparisonEntry :
      ∀ i k : Fin n,
        ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k| =
          2 * (M_inv i k * |T k k|) - idMatrix n i k := by
    intro i k
    calc
      ∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|
          = ∑ j : Fin n,
              (2 * (M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k) -
                M_inv i j * comparisonMatrix n T j k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [comparisonMatrix_abs_eq_two_diag_sub n T j k]
              ring
      _ = 2 * ∑ j : Fin n, M_inv i j * diagMatrix (fun l : Fin n => |T l l|) j k -
            ∑ j : Fin n, M_inv i j * comparisonMatrix n T j k := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (M_inv i k * |T k k|) - idMatrix n i k := by
            rw [hdiagMul i k, hleftEntry i k]
  have happly :
      ∀ i : Fin n,
        ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i =
          higham8_9_comparisonImage n T M_inv x i := by
    intro i
    unfold ch7AmplifiedRhsEF higham8_9_comparisonImage
    calc
      ∑ j : Fin n, |M_inv i j| *
          (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0)
          = ∑ j : Fin n, M_inv i j *
              ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_of_nonneg (hM_nonneg i j)]
              simp
      _ = ∑ k : Fin n,
            (∑ j : Fin n, M_inv i j * |comparisonMatrix n T j k|) * |x k| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ k : Fin n,
            (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hcomparisonEntry i k]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
            ∑ k : Fin n, idMatrix n i k * |x k| := by
            calc
              ∑ k : Fin n, (2 * (M_inv i k * |T k k|) - idMatrix n i k) * |x k|
                  = ∑ k : Fin n,
                      (2 * (M_inv i k * |T k k| * |x k|) -
                        idMatrix n i k * |x k|) := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
              _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| -
                    ∑ k : Fin n, idMatrix n i k * |x k| := by
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, M_inv i k * |T k k| * |x k| - |x i| := by
            simp [idMatrix]
  have hnonneg :
      ∀ i : Fin n, 0 ≤ higham8_9_comparisonImage n T M_inv x i := by
    intro i
    rw [← happly i]
    exact
      ch7AmplifiedRhsEF_nonneg n M_inv
        (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
        (by
          intro a b
          exact abs_nonneg _)
        (by
          intro a
          simp)
        i
  have hforward :
      ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x =
        infNormVec (higham8_9_comparisonImage n T M_inv x) := by
    unfold ch7ForwardBoundEF
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [happly i, ← abs_of_nonneg (hnonneg i)]
      exact abs_le_infNormVec (higham8_9_comparisonImage n T M_inv x) i
    · apply infNormVec_le_of_abs_le
      · intro i
        rw [abs_of_nonneg (hnonneg i), ← happly i]
        exact
          Finset.le_sup'
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x)
            (Finset.mem_univ i)
      · exact
          ch7ForwardBoundEF_nonneg n hn M_inv
            (fun a b => |comparisonMatrix n T a b|) (fun _ => 0) x
            (by
              intro a b
              exact abs_nonneg _)
            (by
              intro a
              simp)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  rw [hforward]

/-- **Lemma 8.9**, inequality part:
`cond(T,x) ≤ cond(M(T),x)` once `|T⁻¹| ≤ M(T)⁻¹` and `M(T)⁻¹ ≥ 0` are known. -/
theorem higham8_9_condAtSolution_le_comparisonMatrix (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (habsInv : ∀ i j : Fin n, |T_inv i j| ≤ M_inv i j)
    (hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := by
  have hnum :
      ch7ForwardBoundEF n hn T_inv (fun a b => |T a b|) (fun _ => 0) x ≤
        ch7ForwardBoundEF n hn M_inv (fun a b => |comparisonMatrix n T a b|)
          (fun _ => 0) x := by
    unfold ch7ForwardBoundEF
    apply Finset.sup'_le
    intro i _
    unfold ch7AmplifiedRhsEF
    calc
      ∑ j : Fin n, |T_inv i j| * (∑ k : Fin n, |T j k| * |x k| + 0)
          ≤ ∑ j : Fin n, M_inv i j * (∑ k : Fin n, |T j k| * |x k| + 0) := by
              apply Finset.sum_le_sum
              intro j _
              have hinner_nonneg : 0 ≤ ∑ k : Fin n, |T j k| * |x k| + 0 := by
                positivity
              exact mul_le_mul_of_nonneg_right (habsInv i j) hinner_nonneg
      _ = ∑ j : Fin n, M_inv i j *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            have hsumEq :
                ∑ k : Fin n, |T j k| * |x k| =
                  ∑ k : Fin n, |comparisonMatrix n T j k| * |x k| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comparisonMatrix_abs_apply]
            rw [hsumEq]
      _ = ∑ j : Fin n, |M_inv i j| *
            (∑ k : Fin n, |comparisonMatrix n T j k| * |x k| + 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_nonneg i j)]
      _ = ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
            (fun _ => 0) x i := by
            rfl
      _ ≤ Finset.sup' Finset.univ
            (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
            (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
              (fun _ => 0) x) := by
            exact
              Finset.le_sup'
                (ch7AmplifiedRhsEF n M_inv (fun a b => |comparisonMatrix n T a b|)
                  (fun _ => 0) x)
                (Finset.mem_univ i)
  unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
  exact div_le_div_of_nonneg_right hnum (infNormVec_nonneg x)

/-- **Lemma 8.9**, upper-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_upperTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv n T T_inv M_inv
      hUT hT_diag hInv hM_RInv hM_inv_ut
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

/-- **Lemma 8.9**, lower-triangular source wrapper:
`cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹ diag(|t_ii|) - I)|x|‖∞ / ‖x‖∞`. -/
theorem higham8_9_lowerTriangular_condAtSolution_le_comparison_eq (n : ℕ) (hn : 0 < n)
    (T T_inv M_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → T i j = 0)
    (hT_diag : ∀ i : Fin n, T i i ≠ 0)
    (hInv : IsInverse n T T_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n T) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤
      infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := by
  have habsInv :=
    abs_inv_le_compMatrix_inv_lowerTri n T T_inv M_inv
      hLT hT_diag hInv hM_RInv hM_inv_lt
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n T i i := by
    intro i
    simp [comparisonMatrix]
    exact hT_diag i
  have hM_offdiag : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n T i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_lt : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n T i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hLT i j hij]
  have hM_nonneg :=
    lower_tri_mmatrix_inv_nonneg n (comparisonMatrix n T) M_inv
      hM_lt hM_diag_pos hM_offdiag hM_RInv hM_inv_lt
  have hle :=
    higham8_9_condAtSolution_le_comparisonMatrix n hn T T_inv M_inv x habsInv hM_nonneg
  have heq :=
    higham8_9_comparisonMatrix_condAtSolution_eq n hn T M_inv x
      hM_nonneg (ch7_isLeftInverse_of_isRightInverse hM_RInv)
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ ch7SkeelCondAtSolutionInf n hn (comparisonMatrix n T) M_inv x := hle
    _ = infNormVec (higham8_9_comparisonImage n T M_inv x) / infNormVec x := heq

/-- **Theorem 8.10**, formalized with Higham's exact `μ` recurrence rather
than an informal `O(u^2)` abbreviation. -/
theorem higham8_10_forwardSub_forward_error_mu_bound (fp : FPModel) (n : ℕ)
    (L L_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n L) M_inv)
    (hM_inv_lt : ∀ i j : Fin n, i.val < j.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_forwardSub fp n L b
    let y := fun i => ∑ j : Fin n, M_inv i j * |b j|
    ∀ i : Fin n, |x i - x_hat i| ≤ mu fp n i.val * y i :=
  forwardSub_forward_error_mu_bound fp n L L_inv M_inv x b hL_diag hLT hInv
    hM_RInv hM_inv_lt hTx hn hn1

/-- **Corollary 8.11**, μ-form for lower triangular M-matrices and `b ≥ 0`. -/
theorem higham8_11_mmatrix_forwardSub_relative_error (fp : FPModel) (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag_pos : ∀ i : Fin n, 0 < L i i)
    (hL_offdiag : ∀ i j : Fin n, j.val < i.val → L i j ≤ 0)
    (hInv : IsInverse n L L_inv)
    (hTx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (h2n : gammaValid fp (2 * n)) :
    let x_hat := fl_forwardSub fp n L b
    (∀ i, 0 ≤ x i) ∧
    (∀ i, 0 ≤ x_hat i) ∧
    (∀ i, |x i - x_hat i| ≤ mu fp n i.val * |x i|) :=
  mmatrix_forwardSub_relative_error fp n L L_inv x b hLT hL_diag_pos
    hL_offdiag hInv hTx hb hn hn1 h2n

/-- **Problem 8.3**, exact `μ`-form for unit upper-triangular substitution.

If `U` is unit upper triangular with `|u_ij| ≤ 1` for `j > i`, then the
comparison-matrix route behind **Theorem 8.10** yields the explicit componentwise
bound

`|x_i - x̂_i| ≤ μ_{n-1-i} 2^(n-1-i) ‖b‖∞`.

This is slightly sharper than the printed source factor `2^(n-i)`, because the
row sum of `M(U)⁻¹` is bounded here by the exact geometric sum
`1 + ∑_{k=0}^{n-i-2} 2^k = 2^(n-1-i)`. -/
theorem higham8_problem8_3_unitUpper_backSub_forward_error_mu_infNorm_bound
    (fp : FPModel) (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_unit : ∀ i : Fin n, U i i = 1)
    (hU_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ 1)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0)
    (hTx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    let x_hat := fl_backSub fp n U b
    ∀ i : Fin n,
      |x i - x_hat i| ≤
        mu fp n (n - 1 - i.val) * 2 ^ (n - 1 - i.val) * infNormVec b := by
  intro x_hat i
  let y : Fin n → ℝ := fun k => ∑ j : Fin n, M_inv k j * |b j|
  have herr_i :
      |x i - x_hat i| ≤ mu fp n (n - 1 - i.val) * y i := by
    simpa [x_hat, y] using
      (backSub_forward_error_mu_bound fp n U U_inv M_inv x b
        (fun k => by rw [hU_unit k]; norm_num)
        hUT hInv hM_RInv hM_inv_ut hTx hn hn1 i)
  have hM_diag_ne : ∀ k : Fin n, comparisonMatrix n U k k ≠ 0 := by
    intro k
    simp [comparisonMatrix, hU_unit k]
  have hM_unit : ∀ k : Fin n, comparisonMatrix n U k k = 1 := by
    intro k
    simp [comparisonMatrix, hU_unit k]
  have hM_bound : ∀ a b : Fin n, a.val < b.val → |comparisonMatrix n U a b| ≤ 1 := by
    intro a b hab
    unfold comparisonMatrix
    simpa [show a ≠ b from Fin.ne_of_val_ne (by omega)] using hU_bound a b hab
  have hM_ut : ∀ a b : Fin n, b.val < a.val → comparisonMatrix n U a b = 0 := by
    intro a b hab
    unfold comparisonMatrix
    simp [show a ≠ b from Fin.ne_of_val_ne (by omega), hUT a b hab]
  have hM_diag_pos : ∀ k : Fin n, 0 < comparisonMatrix n U k k := by
    intro k
    simp [comparisonMatrix, hU_unit k]
  have hM_offdiag : ∀ a b : Fin n, a.val < b.val → comparisonMatrix n U a b ≤ 0 := by
    intro a b hab
    unfold comparisonMatrix
    simp [show a ≠ b from Fin.ne_of_val_ne (by omega)]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_diag : ∀ k : Fin n, M_inv k k = 1 := by
    intro k
    have hM_inv_ut' :=
      inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut hM_diag_ne hM_LInv
    simpa [comparisonMatrix, hU_unit k] using
      inv_diag_entry n (comparisonMatrix n U) M_inv hM_ut hM_diag_ne hM_LInv hM_inv_ut' k
  have hrow_sum : ∑ j : Fin n, M_inv i j ≤ 2 ^ (n - 1 - i.val) := by
    have hsum_abs : ∑ j : Fin n, M_inv i j = ∑ j : Fin n, |M_inv i j| := by
      apply Finset.sum_congr rfl
      intro j _
      exact (abs_of_nonneg (hM_nonneg i j)).symm
    have hsplit :
        ∑ j : Fin n, |M_inv i j| =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), |M_inv i j| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      rw [hM_inv_ut i j hj, abs_zero]
    have hn_pos : 0 < n := by
      exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hfilt_eq :
        Finset.univ.filter (fun j : Fin n => i.val ≤ j.val) =
          Finset.univ.filter (fun j : Fin n =>
            i.val ≤ j.val ∧ j.val ≤ (⟨n - 1, by omega⟩ : Fin n).val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
    calc
      ∑ j : Fin n, M_inv i j = ∑ j : Fin n, |M_inv i j| := hsum_abs
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val ≤ j.val), |M_inv i j| := hsplit
      _ = ∑ j ∈ Finset.univ.filter
            (fun j : Fin n => i.val ≤ j.val ∧
              j.val ≤ (⟨n - 1, by omega⟩ : Fin n).val), |M_inv i j| := by
            rw [hfilt_eq]
      _ ≤ 2 ^ (n - 1 - i.val) := by
            exact inv_row_sum_bound n (comparisonMatrix n U) M_inv
              hM_ut hM_unit hM_bound hM_LInv hM_inv_ut hM_inv_diag
              (n - 1 - i.val) i ⟨n - 1, by omega⟩ (by simp) (by simp; omega)
  have hy_bound : y i ≤ 2 ^ (n - 1 - i.val) * infNormVec b := by
    have hy_le :
        y i ≤ (∑ j : Fin n, M_inv i j) * infNormVec b := by
      unfold y
      calc
        ∑ j : Fin n, M_inv i j * |b j|
            ≤ ∑ j : Fin n, M_inv i j * infNormVec b := by
                  apply Finset.sum_le_sum
                  intro j _
                  exact mul_le_mul_of_nonneg_left (abs_le_infNormVec b j) (hM_nonneg i j)
        _ = (∑ j : Fin n, M_inv i j) * infNormVec b := by
              symm
              exact Finset.sum_mul (Finset.univ) (fun j => M_inv i j) (infNormVec b)
    calc
      y i ≤ (∑ j : Fin n, M_inv i j) * infNormVec b := hy_le
      _ ≤ 2 ^ (n - 1 - i.val) * infNormVec b := by
            exact mul_le_mul_of_nonneg_right hrow_sum (infNormVec_nonneg b)
  calc
    |x i - x_hat i| ≤ mu fp n (n - 1 - i.val) * y i := herr_i
    _ ≤ mu fp n (n - 1 - i.val) * (2 ^ (n - 1 - i.val) * infNormVec b) := by
          exact mul_le_mul_of_nonneg_left hy_bound (mu_nonneg fp n hn1 _)
    _ = mu fp n (n - 1 - i.val) * 2 ^ (n - 1 - i.val) * infNormVec b := by
          ring

/-- An upper-triangular row sum over `univ.erase i` only sees the strict-upper
entries. -/
private lemma higham8_upperTriangular_erase_sum_eq_strictUpper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (i : Fin n) (v : Fin n → ℝ) :
    ∑ j ∈ Finset.univ.erase i, T i j * v j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * v j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
  · intro j hj hnot
    rw [Finset.mem_erase] at hj
    have hnot' : ¬ i.val < j.val := by
      intro hij
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have hji : j.val < i.val := by
      by_contra hge
      push_neg at hge
      exact hj.1 (Fin.ext (by omega))
    rw [hUT i j hji, zero_mul]

/-- For an upper triangular M-matrix, the comparison matrix equals the matrix
itself. -/
private theorem higham8_comparisonMatrix_eq_self_upper (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0) :
    comparisonMatrix n T = T := by
  funext i j
  unfold comparisonMatrix
  by_cases hij : i = j
  · subst hij
    simp [abs_of_pos (hT_diag_pos i)]
  · by_cases hij' : i.val < j.val
    · rw [abs_of_nonpos (hT_offdiag i j hij')]
      simp [hij]
    · have hji : j.val < i.val := by omega
      simp [hij, hUT i j hji]

/-- Exact solutions of upper-triangular M-matrix systems with nonnegative
right-hand side are nonnegative. -/
private theorem higham8_upperTriangularMMatrix_solution_nonneg (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ x i := by
  have hT_diag : ∀ i : Fin n, T i i ≠ 0 := fun i => ne_of_gt (hT_diag_pos i)
  have hInv_ut := inv_upper_tri n T T_inv hUT hT_diag hInv.1
  have hTinv_nonneg :=
    upper_tri_mmatrix_inv_nonneg n T T_inv
      hUT hT_diag_pos hT_offdiag hInv.2 hInv_ut
  have hx_eq : ∀ i : Fin n, x i = ∑ j : Fin n, T_inv i j * b j := by
    intro i
    have hLI := hInv.1 i
    have hsum :
        ∑ j : Fin n, T_inv i j * b j =
          ∑ j : Fin n, T_inv i j * (∑ k : Fin n, T j k * x k) := by
      congr 1
      funext j
      rw [hTx j]
    rw [hsum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hsimp : ∀ k : Fin n,
        (∑ j : Fin n, T_inv i j * T j k) * x k = (if i = k then 1 else 0) * x k := by
      intro k
      congr 1
      exact hLI k
    simp_rw [hsimp]
    simp [Finset.mem_univ]
  intro i
  rw [hx_eq i]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hTinv_nonneg i j) (hb j))

/-- Problem 8.4 row identity for the comparison-image vector under the
upper-triangular M-matrix assumptions. -/
private theorem higham8_problem8_4_comparisonImage_row_eq (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (_hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      T i i * y i =
        T i i * x i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
  intro y i
  have hy_simp : ∀ j : Fin n,
      y j = 2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j := by
    intro j
    unfold y higham8_9_comparisonImage
    rw [abs_of_nonneg (hx_nonneg j)]
    apply congrArg (fun z => 2 * z - x j)
    apply Finset.sum_congr rfl
    intro k _
    rw [abs_of_pos (hT_diag_pos k), abs_of_nonneg (hx_nonneg k)]
  have hTy : ∀ i : Fin n, ∑ j : Fin n, T i j * y j = 2 * T i i * x i - b i := by
    intro i
    calc
      ∑ j : Fin n, T i j * y j
          = ∑ j : Fin n, T i j * (2 * ∑ k : Fin n, T_inv j k * T k k * x k - x j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hy_simp j]
      _ = ∑ j : Fin n,
            (2 * (T i j * ∑ k : Fin n, T_inv j k * T k k * x k) - T i j * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 2 * ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hswap :
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                    = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                calc
                  ∑ j : Fin n, T i j * ∑ k : Fin n, T_inv j k * T k k * x k
                      = ∑ k : Fin n, ∑ j : Fin n, T i j * (T_inv j k * T k k * x k) := by
                          simp_rw [Finset.mul_sum]
                          rw [Finset.sum_comm]
                  _ = ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                        apply Finset.sum_congr rfl
                        intro k _
                        calc
                          ∑ j : Fin n, T i j * (T_inv j k * T k k * x k)
                              = ∑ j : Fin n, (T i j * T_inv j k) * (T k k * x k) := by
                                  apply Finset.sum_congr rfl
                                  intro j _
                                  ring
                          _ = (∑ j : Fin n, T i j * T_inv j k) * (T k k * x k) := by
                                  rw [Finset.sum_mul]
                          _ = (∑ j : Fin n, T i j * T_inv j k) * T k k * x k := by
                                  ring
              rw [hswap]
      _ = 2 * ∑ k : Fin n, idMatrix n i k * T k k * x k -
            ∑ j : Fin n, T i j * x j := by
              have hid :
                  ∑ k : Fin n, (∑ j : Fin n, T i j * T_inv j k) * T k k * x k
                    = ∑ k : Fin n, idMatrix n i k * T k k * x k := by
                apply Finset.sum_congr rfl
                intro k _
                have hright := congrArg (fun z => z * (T k k * x k)) (hInv.2 i k)
                simpa [idMatrix, mul_assoc] using hright
              rw [hid]
      _ = 2 * (T i i * x i) - b i := by
              rw [hTx i]
              simp [idMatrix]
      _ = 2 * T i i * x i - b i := by
              ring
  have hTx_split :
      T i i * x i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j = b i := by
    have h := hTx i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at h
    simpa using h
  have hTy_split :
      T i i * y i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          2 * T i i * x i - b i := by
    have h := hTy i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i y] at h
    simpa using h
  have hTx_pos :
      T i i * x i =
        b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTx_split
    linarith
  have hTy_pos :
      T i i * y i =
        2 * T i i * x i - b i +
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
    have hsum :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * y j =
          -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum] at hTy_split
    linarith
  linarith

/-- Problem 8.4 componentwise bound for the comparison-image vector:
`(2T⁻¹ diag(t_ii) - I)x ≤ (2(n-i)-1) x`. -/
private theorem higham8_problem8_4_comparisonImage_nonneg_bound (n : ℕ)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    let y := higham8_9_comparisonImage n T T_inv x
    ∀ i : Fin n,
      0 ≤ y i ∧
      y i ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := by
  intro y
  have hrow :=
    higham8_problem8_4_comparisonImage_row_eq n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hx_nonneg
  suffices h :
      ∀ d : ℕ, ∀ i : Fin n, n - 1 - i.val ≤ d →
        0 ≤ y i ∧ y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i by
    intro i
    simpa using h (n - 1 - i.val) i (le_refl _)
  intro d
  induction d with
  | zero =>
      intro i hi
      have hi_last : i.val = n - 1 := by omega
      have hsumx_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hsumy_zero :
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        omega
      have hy_eq : y i = x i := by
        have hscaled : T i i * y i = T i i * x i := by
          have hrowi := hrow i
          rw [hsumx_zero, hsumy_zero, add_zero, add_zero] at hrowi
          simpa [y] using hrowi
        exact mul_left_cancel₀ (ne_of_gt (hT_diag_pos i)) hscaled
      refine ⟨?_, ?_⟩
      · simpa [hy_eq] using hx_nonneg i
      · rw [hy_eq]
        simp
  | succ d ih =>
      intro i hi
      by_cases htail : n - 1 - i.val ≤ d
      · rcases ih i htail with ⟨hy_nonneg, hy_le⟩
        refine ⟨hy_nonneg, ?_⟩
        calc
          y i ≤ (((2 * d + 1 : ℕ) : ℝ)) * x i := hy_le
          _ ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i := by
                have hcoef :
                    (((2 * d + 1 : ℕ) : ℝ)) ≤ (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  norm_num
                exact mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
      · let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val < j.val)
        let sx : ℝ := ∑ j ∈ S, (-T i j) * x j
        let sy : ℝ := ∑ j ∈ S, (-T i j) * y j
        have hrowi : T i i * y i = T i i * x i + sx + sy := by
          simpa [S, sx, sy, add_assoc, add_left_comm, add_comm] using hrow i
        have hsx_nonneg : 0 ≤ sx := by
          unfold sx S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (hx_nonneg j)
        have hsy_nonneg : 0 ≤ sy := by
          unfold sy S
          apply Finset.sum_nonneg
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hj_tail : n - 1 - j.val ≤ d := by omega
          exact mul_nonneg (by linarith [hT_offdiag i j hj]) (ih j hj_tail).1
        have hsx_le : sx ≤ T i i * x i := by
          have hTx_pos :
              T i i * x i = b i + sx := by
            have hTxi := hTx i
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hTxi
            rw [higham8_upperTriangular_erase_sum_eq_strictUpper n T hUT i x] at hTxi
            unfold sx S
            have hsum :
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), T i j * x j =
                  -∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (-T i j) * x j := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum] at hTxi
            linarith
          linarith [hb i, hTx_pos]
        have hsy_le : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * sx := by
          unfold sy sx S
          calc
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * y j
                ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                    (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by
                    apply Finset.sum_le_sum
                    intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    have hj_tail : n - 1 - j.val ≤ d := by omega
                    have hy_le : y j ≤ (((2 * d + 1 : ℕ) : ℝ)) * x j := (ih j hj_tail).2
                    have hcoef_nonneg : 0 ≤ -T i j := by linarith [hT_offdiag i j hj]
                    calc
                      (-T i j) * y j ≤ (-T i j) * ((((2 * d + 1 : ℕ) : ℝ)) * x j) :=
                        mul_le_mul_of_nonneg_left hy_le hcoef_nonneg
                      _ = (((2 * d + 1 : ℕ) : ℝ)) * ((-T i j) * x j) := by ring
            _ = (((2 * d + 1 : ℕ) : ℝ)) *
                  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), (-T i j) * x j := by
                    rw [← Finset.mul_sum]
        have hy_nonneg : 0 ≤ y i := by
          have hprod_nonneg : 0 ≤ T i i * y i := by
            linarith [hrowi, hsx_nonneg, hsy_nonneg, hx_nonneg i, hT_diag_pos i]
          by_contra hyneg
          push_neg at hyneg
          linarith [mul_neg_of_pos_of_neg (hT_diag_pos i) hyneg]
        have hc_nonneg : 0 ≤ (((2 * d + 1 : ℕ) : ℝ)) := by
          positivity
        have hsy_le' : sy ≤ (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
          exact le_trans hsy_le (mul_le_mul_of_nonneg_left hsx_le hc_nonneg)
        have hcoef_eq :
            (2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ)) = (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
          norm_num
          ring
        have hscaled :
            T i i * y i ≤
              T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
          calc
            T i i * y i = T i i * x i + sx + sy := hrowi
            _ ≤ T i i * x i + T i i * x i + (((2 * d + 1 : ℕ) : ℝ)) * (T i i * x i) := by
                  linarith
            _ = (T i i * x i) * ((2 : ℝ) + (((2 * d + 1 : ℕ) : ℝ))) := by
                  ring
            _ = (T i i * x i) * (((2 * (d + 1) + 1 : ℕ) : ℝ)) := by
                  rw [hcoef_eq]
            _ = T i i * (x i * (((2 * (d + 1) + 1 : ℕ) : ℝ))) := by
                  rw [mul_assoc]
            _ = T i i * ((((2 * (d + 1) + 1 : ℕ) : ℝ)) * x i) := by
                  congr 1
                  rw [mul_comm]
        refine ⟨hy_nonneg, ?_⟩
        exact le_of_mul_le_mul_left hscaled (hT_diag_pos i)

/-- **Problem 8.4**: if `T` is an upper triangular M-matrix and `b = Tx ≥ 0`,
then `cond(T,x) ≤ 2n-1`. -/
theorem higham8_4_upperTriangularMMatrix_condAtSolution_le (n : ℕ) (hn : 0 < n)
    (T T_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → T i j = 0)
    (hT_diag_pos : ∀ i : Fin n, 0 < T i i)
    (hT_offdiag : ∀ i j : Fin n, i.val < j.val → T i j ≤ 0)
    (hInv : IsInverse n T T_inv)
    (hTx : ∀ i, ∑ j : Fin n, T i j * x j = b i)
    (hb : ∀ i, 0 ≤ b i)
    (hx : 0 < infNormVec x) :
    ch7SkeelCondAtSolutionInf n hn T T_inv x ≤ 2 * (n : ℝ) - 1 := by
  have hx_nonneg :=
    higham8_upperTriangularMMatrix_solution_nonneg n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb
  have hComp :
      comparisonMatrix n T = T :=
    higham8_comparisonMatrix_eq_self_upper n T hUT hT_diag_pos hT_offdiag
  have hInv_ut :=
    inv_upper_tri n T T_inv hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv.1
  have hy_bound :=
    higham8_problem8_4_comparisonImage_nonneg_bound n T T_inv x b
      hUT hT_diag_pos hT_offdiag hInv hTx hb hx_nonneg
  have hcoef_nonneg : 0 ≤ 2 * (n : ℝ) - 1 := by
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hn
    linarith
  have hy_norm :
      infNormVec (higham8_9_comparisonImage n T T_inv x) ≤
        (2 * (n : ℝ) - 1) * infNormVec x := by
    apply infNormVec_le_of_abs_le
    · intro i
      rcases hy_bound i with ⟨hy_nonneg, hy_le⟩
      rw [abs_of_nonneg hy_nonneg]
      have hcoef_nat : 2 * (n - 1 - i.val) + 1 ≤ 2 * n - 1 := by omega
      have hcoef :
          (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) - 1 := by
        have hcoef' :
            (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) ≤ (((2 * n - 1 : ℕ) : ℝ)) := by
          exact_mod_cast hcoef_nat
        have htarget : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
          have htwo : 1 ≤ 2 * n := by
            have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
            omega
          rw [Nat.cast_sub htwo, Nat.cast_mul, Nat.cast_one]
          ring
        rw [htarget] at hcoef'
        exact hcoef'
      have hxi_le : x i ≤ infNormVec x := by
        simpa [abs_of_nonneg (hx_nonneg i)] using abs_le_infNormVec x i
      calc
        higham8_9_comparisonImage n T T_inv x i
            ≤ (((2 * (n - 1 - i.val) + 1 : ℕ) : ℝ)) * x i := hy_le
        _ ≤ (2 * (n : ℝ) - 1) * x i :=
              mul_le_mul_of_nonneg_right hcoef (hx_nonneg i)
        _ ≤ (2 * (n : ℝ) - 1) * infNormVec x :=
              mul_le_mul_of_nonneg_left hxi_le hcoef_nonneg
    ·
      exact mul_nonneg hcoef_nonneg (infNormVec_nonneg x)
  have hcond_le :=
    higham8_9_upperTriangular_condAtSolution_le_comparison_eq n hn T T_inv T_inv x
      hUT (fun i => ne_of_gt (hT_diag_pos i)) hInv
      (by simpa [hComp] using hInv.2) hInv_ut
  calc
    ch7SkeelCondAtSolutionInf n hn T T_inv x
        ≤ infNormVec (higham8_9_comparisonImage n T T_inv x) / infNormVec x := hcond_le
    _ ≤ ((2 * (n : ℝ) - 1) * infNormVec x) / infNormVec x :=
          div_le_div_of_nonneg_right hy_norm (infNormVec_nonneg x)
    _ = 2 * (n : ℝ) - 1 := by
          field_simp [ne_of_gt hx]

/-! ## §8.3 Bounds for the Inverse -/

/-- **Equation (8.7)**: Higham's comparison matrix. -/
noncomputable def higham8_7_comparisonMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  comparisonMatrix n A

/-- **Theorem 8.12**, first comparison-matrix inverse inequality. -/
theorem higham8_12_abs_inv_le_comparison_inv (n : ℕ)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j :=
  abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut

/-- **Theorem 8.12**: the strict-upper row maximum used to define `W(U)`. -/
noncomputable def higham8_12_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
      (by
        refine ⟨⟨i.val + 1, h⟩, ?_⟩
        simp [Finset.mem_filter]
        exact Fin.lt_def.mpr (by simp))
      (fun j => |U i j|)
  else
    0

/-- The strict-upper row maximum is nonnegative. -/
lemma higham8_12_rowMaxStrictUpper_nonneg (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham8_12_rowMaxStrictUpper n U i := by
  by_cases h : i.val + 1 < n
  · have hmem :
        (⟨i.val + 1, h⟩ : Fin n) ∈
          Finset.univ.filter (fun j : Fin n => i.val < j.val) := by
      simp [Finset.mem_filter]
      exact Fin.lt_def.mpr (by simp)
    have hs :
        |U i ⟨i.val + 1, h⟩| ≤
          Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
            ⟨⟨i.val + 1, h⟩, hmem⟩ (fun j => |U i j|) :=
      Finset.le_sup' (fun j => |U i j|) hmem
    simpa [higham8_12_rowMaxStrictUpper, h] using
      (le_trans (abs_nonneg _) hs)
  · simp [higham8_12_rowMaxStrictUpper, h]

/-- Any strict-upper entry is bounded by the corresponding row maximum. -/
lemma higham8_12_abs_le_rowMaxStrictUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    |U i j| ≤ higham8_12_rowMaxStrictUpper n U i := by
  have hsucc : i.val + 1 < n := by omega
  have hs :
      |U i j| ≤
        Finset.sup' (Finset.univ.filter (fun k : Fin n => i.val < k.val))
          (by
            refine ⟨⟨i.val + 1, hsucc⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun k => |U i k|) :=
    Finset.le_sup' (fun k => |U i k|) (by
      show j ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val)
      exact Finset.mem_filter.mpr ⟨by simp, hij⟩)
  simpa [higham8_12_rowMaxStrictUpper, hsucc] using hs

/-- **Theorem 8.12**: Higham's row-max minorant `W(U)`. -/
noncomputable def higham8_12_WMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then |U i i|
    else if i.val < j.val then -(higham8_12_rowMaxStrictUpper n U i)
    else 0

/-- `W(U)` is upper triangular by construction. -/
lemma higham8_12_WMatrix_upper (n : ℕ) (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_WMatrix n U i j = 0 := by
  intro i j hij
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_WMatrix, hnotlt,
    show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The diagonal of `W(U)` is the absolute diagonal of `U`. -/
lemma higham8_12_WMatrix_diag (n : ℕ) (U : Fin n → Fin n → ℝ) (i : Fin n) :
    higham8_12_WMatrix n U i i = |U i i| := by
  simp [higham8_12_WMatrix]

/-- Strict-upper entries of `W(U)` are the negated row maxima. -/
lemma higham8_12_WMatrix_strictUpper (n : ℕ) (U : Fin n → Fin n → ℝ)
    {i j : Fin n} (hij : i.val < j.val) :
    higham8_12_WMatrix n U i j = -(higham8_12_rowMaxStrictUpper n U i) := by
  simp [higham8_12_WMatrix, hij, show ¬ i = j from Fin.ne_of_val_ne (by omega)]

/-- The comparison matrix dominates `W(U)` entrywise for upper-triangular `U`. -/
lemma higham8_12_WMatrix_le_comparisonMatrix (n : ℕ)
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i j : Fin n, higham8_12_WMatrix n U i j ≤ comparisonMatrix n U i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [higham8_12_WMatrix, comparisonMatrix]
  · by_cases hlt : i.val < j.val
    · rw [higham8_12_WMatrix_strictUpper n U hlt]
      simpa [comparisonMatrix, hij] using
        (neg_le_neg (higham8_12_abs_le_rowMaxStrictUpper n U i j hlt))
    · have hji : j.val < i.val := by omega
      rw [higham8_12_WMatrix_upper n U i j hji]
      simp [comparisonMatrix, hij, hUT i j hji]

/-- The row maxima satisfy the source `β` bound when every strict-upper entry
is bounded by `β |u_ii|`. -/
lemma higham8_12_rowMaxStrictUpper_le_beta_mul_diag (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    ∀ i : Fin n, higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| := by
  intro i
  by_cases h : i.val + 1 < n
  · have hs :
        Finset.sup' (Finset.univ.filter (fun j : Fin n => i.val < j.val))
          (by
            refine ⟨⟨i.val + 1, h⟩, ?_⟩
            simp [Finset.mem_filter]
            exact Fin.lt_def.mpr (by simp))
          (fun j => |U i j|) ≤ β * |U i i| := by
      apply Finset.sup'_le
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hβ_bound i j hj
    simpa [higham8_12_rowMaxStrictUpper, h] using hs
  · simpa [higham8_12_rowMaxStrictUpper, h] using
      (mul_nonneg hβ (abs_nonneg _))

/-- Under `β ≤ 1`, Higham's `W(U)` satisfies the repository's diagonal-dominant
upper-triangular condition (8.5). -/
theorem higham8_12_WMatrix_isDiagDominantUpper (n : ℕ)
    (U : Fin n → Fin n → ℝ) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    IsDiagDominantUpper n (higham8_12_WMatrix n U) := by
  refine ⟨higham8_12_WMatrix_upper n U, ?_, ?_⟩
  · intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_ne_zero.mpr (hU_diag i)
  · intro i j hij
    rw [higham8_12_WMatrix_diag, higham8_12_WMatrix_strictUpper n U hij]
    rw [abs_abs, abs_neg, abs_of_nonneg (higham8_12_rowMaxStrictUpper_nonneg n U i)]
    calc
      higham8_12_rowMaxStrictUpper n U i ≤ β * |U i i| :=
        higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i
      _ ≤ |U i i| := by
        have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg _
        nlinarith

/-- **Theorem 8.14 support**: once `W(U)` is known to satisfy the source
`β ≤ 1` hypothesis, the existing diagonal-dominant inverse API gives the
rightmost `∞`-norm upper bound for `W(U)⁻¹`. -/
theorem higham8_14_WInv_infNorm_upperBound (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (i0 : Fin n) {β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hInv : IsInverse n (higham8_12_WMatrix n U) W_inv) :
    infNorm W_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) := by
  have hDD :=
    higham8_12_WMatrix_isDiagDominantUpper n U hU_diag hβ hβ1 hβ_bound
  simpa [higham8_12_WMatrix] using
    triInv_infNorm_upperBound n (higham8_12_WMatrix n U) W_inv i0 hDD hInv

/-- **Theorem 8.12**: the source `Z` minorant with diagonal `α` and strict
upper entries `-αβ`. -/
noncomputable def higham8_12_ZMatrix (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => α * higham8_3_stressUpper n β i j

/-- Explicit inverse formula for the source `Z` matrix. -/
noncomputable def higham8_12_ZInvFormula (n : ℕ) (α β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / α) * higham8_4_stressUpperInvFormula n β i j

/-- The explicit `Z` inverse formula has the same scaled column sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_col_sum (n : ℕ) (α β : ℝ) (j : Fin n) :
    ∑ i : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ j.val := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_col_sum]

/-- The explicit `Z` inverse formula has the same scaled row sums as the
stress-family inverse. -/
theorem higham8_12_ZInvFormula_row_sum (n : ℕ) (α β : ℝ) (i : Fin n) :
    ∑ j : Fin n, higham8_12_ZInvFormula n α β i j =
      (1 / α) * (1 + β) ^ (n - 1 - i.val) := by
  unfold higham8_12_ZInvFormula
  rw [← Finset.mul_sum, higham8_4_stressUpperInvFormula_row_sum]

/-- The explicit inverse formula is a genuine right inverse of the source `Z`
matrix. -/
theorem higham8_12_ZInvFormula_isRightInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsRightInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  intro i j
  calc
    ∑ k : Fin n, higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j
        =
      ∑ k : Fin n,
        higham8_3_stressUpper n β i k * higham8_4_stressUpperInvFormula n β k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          unfold higham8_12_ZMatrix higham8_12_ZInvFormula
          field_simp [hα]
    _ = (if i = j then 1 else 0) :=
      higham8_4_stressUpperInvFormula_isRightInverse n β i j

/-- The explicit inverse formula is a genuine two-sided inverse of the source
`Z` matrix. -/
theorem higham8_12_ZInvFormula_isInverse (n : ℕ) (α β : ℝ) (hα : α ≠ 0) :
    IsInverse n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β) := by
  have hRight := higham8_12_ZInvFormula_isRightInverse n α β hα
  exact ⟨ch7_isLeftInverse_of_isRightInverse hRight, hRight⟩

/-- The explicit `Z` inverse formula is entrywise nonnegative for `α > 0` and
`β ≥ 0`. -/
lemma higham8_12_ZInvFormula_nonneg (n : ℕ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ i j : Fin n, 0 ≤ higham8_12_ZInvFormula n α β i j := by
  intro i j
  unfold higham8_12_ZInvFormula
  have hscale : 0 ≤ 1 / α := one_div_nonneg.mpr hα.le
  by_cases hij : i = j
  · simpa [higham8_4_stressUpperInvFormula, hij] using hscale
  · by_cases hlt : i.val < j.val
    · have hpow : 0 ≤ (1 + β) ^ (j.val - i.val - 1) := by
        apply pow_nonneg
        linarith
      rw [higham8_4_stressUpperInvFormula, if_neg hij, if_pos hlt]
      exact mul_nonneg hscale (mul_nonneg hβ hpow)
    · simp [higham8_4_stressUpperInvFormula, hij, hlt]

private lemma higham8_12_WMatrix_offdiag_nonpos (n : ℕ)
    (U : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val < j.val → higham8_12_WMatrix n U i j ≤ 0 := by
  intro i j hij
  rw [higham8_12_WMatrix_strictUpper n U hij]
  exact neg_nonpos.mpr (higham8_12_rowMaxStrictUpper_nonneg n U i)

private lemma higham8_12_ZMatrix_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZMatrix n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hnotlt]

private lemma higham8_12_ZInvFormula_upper (n : ℕ) (α β : ℝ) :
    ∀ i j : Fin n, j.val < i.val → higham8_12_ZInvFormula n α β i j = 0 := by
  intro i j hij
  have hneq : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hnotlt : ¬ i.val < j.val := by omega
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula, hneq, hnotlt]

private lemma higham8_12_ZInvFormula_diag (n : ℕ) (α β : ℝ) (i : Fin n) :
    higham8_12_ZInvFormula n α β i i = 1 / α := by
  simp [higham8_12_ZInvFormula, higham8_4_stressUpperInvFormula]

/-- **Theorem 8.12**, middle inverse-chain step `M(U)⁻¹ ≤ W(U)⁻¹`. -/
theorem higham8_12_comparisonInv_le_WInv (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, M_inv i j ≤ W_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        M_inv i j ≤ W_inv i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hM_inv_ut i j (by omega), hW_inv_ut i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hM_diag :
          M_inv i i = 1 / |U i i| := by
        simpa [comparisonMatrix] using
          inv_diag_entry n (comparisonMatrix n U) M_inv
            hM_ut (fun k => ne_of_gt (hM_diag_pos k)) hM_LInv hM_inv_ut i
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      rw [hM_diag, hW_diag]
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_M :=
          inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
            (fun k => ne_of_gt (hM_diag_pos k)) hM_RInv hM_inv_ut i j hij'
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hM_prod :
            |U i i| * M_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  comparisonMatrix n U i k * M_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    |U i k| * M_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp [comparisonMatrix, show i ≠ k from Fin.ne_of_val_ne (by omega)]
          have hM_ii : comparisonMatrix n U i i = |U i i| := by
            simp [comparisonMatrix]
          rw [hM_ii] at hrec_M
          rw [hsum_rw] at hrec_M
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                |U i k| * M_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              |U i k| * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * M_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_abs_le_rowMaxStrictUpper n U i k hk.1)
              (hM_nonneg k j)
          have hih :
              higham8_12_rowMaxStrictUpper n U i * M_inv k j ≤
                higham8_12_rowMaxStrictUpper n U i * W_inv k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (higham8_12_rowMaxStrictUpper_nonneg n U i)
          exact hrow_le.trans hih
        calc
          M_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  |U i k| * M_inv k j) / |U i i| := by
              rw [← hM_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ = W_inv i j := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]

/-- **Theorem 8.12**, last middle inverse-chain step `W(U)⁻¹ ≤ Z(U)⁻¹`. -/
theorem higham8_12_WInv_le_ZInvFormula (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, W_inv i j ≤ higham8_12_ZInvFormula n α β i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  have hW_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U) hW_diag_pos
      (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut
  have hZ_RInv := higham8_12_ZInvFormula_isRightInverse n α β (ne_of_gt hα)
  suffices h :
      ∀ (d : ℕ), ∀ i j : Fin n, j.val - i.val ≤ d → i.val ≤ j.val →
        W_inv i j ≤ higham8_12_ZInvFormula n α β i j from
    fun i j => by
      by_cases hij : i.val ≤ j.val
      · exact h (j.val - i.val) i j (le_refl _) hij
      · push_neg at hij
        rw [hW_inv_ut i j (by omega), higham8_12_ZInvFormula_upper n α β i j (by omega)]
  intro d
  induction d with
  | zero =>
      intro i j hdiff hij
      have heq : i = j := Fin.ext (by omega)
      subst heq
      have hW_diag :
          W_inv i i = 1 / |U i i| := by
        simpa [higham8_12_WMatrix] using
          inv_diag_entry n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_LInv hW_inv_ut i
      have hdiag_le : 1 / |U i i| ≤ 1 / α := by
        exact one_div_le_one_div_of_le hα (hα_le_diag i)
      rw [hW_diag, higham8_12_ZInvFormula_diag]
      exact hdiag_le
  | succ d ih =>
      intro i j hdiff hij
      by_cases heq : i.val = j.val
      · exact ih i j (by omega) (by omega)
      · have hij' : i.val < j.val := by omega
        have hUii_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hrec_W :=
          inv_recurrence n (higham8_12_WMatrix n U) W_inv
            (higham8_12_WMatrix_upper n U)
            (fun k => ne_of_gt (hW_diag_pos k)) hW_RInv hW_inv_ut i j hij'
        have hZ_prod :
            α * higham8_12_ZInvFormula n α β i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (α * β) * higham8_12_ZInvFormula n α β k j := by
          have hZ_diag_pos : ∀ i : Fin n, 0 < higham8_12_ZMatrix n α β i i := by
            intro k
            simpa [higham8_12_ZMatrix, higham8_3_stressUpper] using hα
          have hrec_Z :=
            inv_recurrence n (higham8_12_ZMatrix n α β) (higham8_12_ZInvFormula n α β)
              (higham8_12_ZMatrix_upper n α β)
              (fun k => ne_of_gt (hZ_diag_pos k)) hZ_RInv
              (higham8_12_ZInvFormula_upper n α β) i j hij'
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_ZMatrix n α β i k * higham8_12_ZInvFormula n α β k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    (α * β) * higham8_12_ZInvFormula n α β k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hneq : i ≠ k := Fin.ne_of_val_ne (by omega)
            simp [higham8_12_ZMatrix, higham8_3_stressUpper, hneq, hk.1]
          have hZ_ii : higham8_12_ZMatrix n α β i i = α := by
            simp [higham8_12_ZMatrix, higham8_3_stressUpper]
          rw [hZ_ii] at hrec_Z
          rw [hsum_rw] at hrec_Z
          linarith
        have hW_prod :
            |U i i| * W_inv i j =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j := by
          have hsum_rw :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_WMatrix n U i k * W_inv k j =
                -(∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    higham8_12_rowMaxStrictUpper n U i * W_inv k j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            rw [higham8_12_WMatrix_strictUpper n U hk.1]
            ring
          rw [higham8_12_WMatrix_diag] at hrec_W
          rw [hsum_rw] at hrec_W
          linarith
        have hsum_le :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have hrow_le :
              higham8_12_rowMaxStrictUpper n U i * W_inv k j ≤
                (β * |U i i|) * W_inv k j :=
            mul_le_mul_of_nonneg_right
              (higham8_12_rowMaxStrictUpper_le_beta_mul_diag n U hβ hβ_bound i)
              (hW_nonneg k j)
          have hih :
              (β * |U i i|) * W_inv k j ≤
                (β * |U i i|) * higham8_12_ZInvFormula n α β k j :=
            mul_le_mul_of_nonneg_left
              (ih k j (by omega) (by omega))
              (mul_nonneg hβ (abs_nonneg _))
          exact hrow_le.trans hih
        have hZ_beta_sum :
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j =
              higham8_12_ZInvFormula n α β i j := by
          have hsum_factor :
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (α * β) * higham8_12_ZInvFormula n α β k j =
                α *
                  (∑ k ∈ Finset.univ.filter
                      (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                      β * higham8_12_ZInvFormula n α β k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
          calc
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j
                =
              (α *
                (∑ k ∈ Finset.univ.filter
                    (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                    β * higham8_12_ZInvFormula n α β k j)) / α := by
                  field_simp [ne_of_gt hα]
            _ =
              (α * higham8_12_ZInvFormula n α β i j) / α := by
                rw [← hsum_factor, hZ_prod]
            _ = higham8_12_ZInvFormula n α β i j := by
                field_simp [ne_of_gt hα]
        calc
          W_inv i j =
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  higham8_12_rowMaxStrictUpper n U i * W_inv k j) / |U i i| := by
              rw [← hW_prod]
              field_simp [ne_of_gt hUii_pos]
          _ ≤
              (∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                  (β * |U i i|) * higham8_12_ZInvFormula n α β k j) / |U i i| :=
                div_le_div_of_nonneg_right hsum_le (le_of_lt hUii_pos)
          _ =
              ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val),
                β * higham8_12_ZInvFormula n α β k j := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k hk
              field_simp [ne_of_gt hUii_pos]
          _ = higham8_12_ZInvFormula n α β i j := hZ_beta_sum

private theorem higham8_12_comparisonInv_nonneg (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv) :
    ∀ i j : Fin n, 0 ≤ M_inv i j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut :=
    inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
      (fun i => ne_of_gt (hM_diag_pos i)) hM_LInv
  exact upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut

private theorem higham8_12_WInv_nonneg (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i j : Fin n, 0 ≤ W_inv i j := by
  have hW_diag_pos : ∀ i : Fin n, 0 < higham8_12_WMatrix n U i i := by
    intro i
    rw [higham8_12_WMatrix_diag]
    exact abs_pos.mpr (hU_diag i)
  have hW_LInv := ch7_isLeftInverse_of_isRightInverse hW_RInv
  have hW_inv_ut :=
    inv_upper_tri n (higham8_12_WMatrix n U) W_inv
      (higham8_12_WMatrix_upper n U)
      (fun i => ne_of_gt (hW_diag_pos i)) hW_LInv
  exact upper_tri_mmatrix_inv_nonneg n (higham8_12_WMatrix n U) W_inv
    (higham8_12_WMatrix_upper n U) hW_diag_pos
    (higham8_12_WMatrix_offdiag_nonpos n U) hW_RInv hW_inv_ut

private theorem higham8_infNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |A i j| ≤ ∑ j : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hAB i j
      _ = ∑ j : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ infNorm B := row_sum_le_infNorm B i
  · exact infNorm_nonneg B

private theorem higham8_oneNorm_le_of_abs_le_nonneg {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply oneNorm_le_of_col_sum_le
  · intro j
    calc
      ∑ i : Fin n, |A i j| ≤ ∑ i : Fin n, B i j := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hAB i j
      _ = ∑ i : Fin n, |B i j| := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (abs_of_nonneg (hB_nonneg i j)).symm
      _ ≤ oneNorm B := col_sum_le_oneNorm B j
  · exact oneNorm_nonneg B

private theorem higham8_infNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    infNorm A ≤ infNorm B := by
  apply higham8_infNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_oneNorm_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    oneNorm A ≤ oneNorm B := by
  apply higham8_oneNorm_le_of_abs_le_nonneg A B hB_nonneg
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_opNorm2_le_of_abs_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hAB : ∀ i j : Fin n, |A i j| ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  have hB_rect :
      rectOpNorm2Le B (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le B le_rfl
  have hA_rect :
      rectOpNorm2Le A (complexMatrixOp2 (realRectToCMatrix B)) :=
    rectOpNorm2Le_of_abs_entry_le hAB hB_rect
  exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A
    (complexMatrixOp2_nonneg (realRectToCMatrix B)) hA_rect

private theorem higham8_opNorm2_le_of_nonneg_le {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) :
    complexMatrixOp2 (realRectToCMatrix A) ≤
      complexMatrixOp2 (realRectToCMatrix B) := by
  apply higham8_opNorm2_le_of_abs_le A B
  intro i j
  rw [abs_of_nonneg (hA_nonneg i j)]
  exact hAB i j

private theorem higham8_nonneg_real_matrix_absVec_mul_norm {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (z : CVec n) (i : Fin n) :
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖ =
      ∑ j : Fin n, A i j * ‖z j‖ := by
  have hA_abs_eq : absMatrixRect A = A := by
    ext i j
    simp [absMatrixRect, hA_nonneg i j]
  have hA_abs :
      complexAbsMatrix (realRectToCMatrix A) = realRectToCMatrix A := by
    simpa [hA_abs_eq] using (realRectToCMatrix_absMatrixRect A).symm
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ‖complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix A))
            (complexAbsVec z) i‖ := by
              rw [hA_abs]
    _ = ∑ j : Fin n, ‖realRectToCMatrix A i j‖ * ‖z j‖ := by
          exact
            complexMatrixVecMul_absMatrix_absVec_norm_apply
              (realRectToCMatrix A) z i
    _ = ∑ j : Fin n, A i j * ‖z j‖ := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [realRectToCMatrix, hA_nonneg i j]

private theorem higham8_absolute_norm_vec_le_of_nonneg_le {n : ℕ}
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (A B : Fin n → Fin n → ℝ)
    (hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j)
    (hB_nonneg : ∀ i j : Fin n, 0 ≤ B i j)
    (hAB : ∀ i j : Fin n, A i j ≤ B i j) (z : CVec n) :
    ν (complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z)) ≤
      ν (complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z)) := by
  have hmono : IsMonotoneComplexVectorNorm ν :=
    (absolute_norm_iff_monotone_norm hν).mp habs
  apply hmono
  intro i
  calc
    ‖complexMatrixVecMul (realRectToCMatrix A) (complexAbsVec z) i‖
        = ∑ j : Fin n, A i j * ‖z j‖ :=
          higham8_nonneg_real_matrix_absVec_mul_norm A hA_nonneg z i
    _ ≤ ∑ j : Fin n, B i j * ‖z j‖ := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_right (hAB i j) (norm_nonneg (z j))
    _ = ‖complexMatrixVecMul (realRectToCMatrix B) (complexAbsVec z) i‖ := by
          symm
          exact higham8_nonneg_real_matrix_absVec_mul_norm B hB_nonneg z i

/-- **Theorem 8.12**, `∞`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_infNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    infNorm U_inv ≤ infNorm M_inv ∧
      infNorm M_inv ≤ infNorm W_inv ∧
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      infNorm U_inv ≤ infNorm M_inv :=
    higham8_infNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      infNorm M_inv ≤ infNorm W_inv :=
    higham8_infNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) :=
    higham8_infNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, `1`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_oneNorm_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ oneNorm M_inv ∧
      oneNorm M_inv ≤ oneNorm W_inv ∧
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      oneNorm U_inv ≤ oneNorm M_inv :=
    higham8_oneNorm_le_of_abs_le_nonneg U_inv M_inv hM_nonneg
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      oneNorm M_inv ≤ oneNorm W_inv :=
    higham8_oneNorm_le_of_nonneg_le M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) :=
    higham8_oneNorm_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, `2`-norm chain induced by the entrywise inverse chain. -/
theorem higham8_12_opNorm2_chain (n : ℕ)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) ∧
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) ∧
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hUM :
      complexMatrixOp2 (realRectToCMatrix U_inv) ≤
        complexMatrixOp2 (realRectToCMatrix M_inv) :=
    higham8_opNorm2_le_of_abs_le U_inv M_inv
      (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
        hUT hU_diag hInv hM_RInv
        (inv_upper_tri n (comparisonMatrix n U) M_inv
          (by
            intro i j hij
            unfold comparisonMatrix
            simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
          (by
            intro i
            simp [comparisonMatrix, hU_diag i])
          (ch7_isLeftInverse_of_isRightInverse hM_RInv)))
  have hMW :
      complexMatrixOp2 (realRectToCMatrix M_inv) ≤
        complexMatrixOp2 (realRectToCMatrix W_inv) :=
    higham8_opNorm2_le_of_nonneg_le M_inv W_inv hM_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv)
  have hWZ :
      complexMatrixOp2 (realRectToCMatrix W_inv) ≤
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) :=
    higham8_opNorm2_le_of_nonneg_le W_inv (higham8_12_ZInvFormula n α β)
      hW_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv)
  exact ⟨hUM, hMW, hWZ⟩

/-- **Theorem 8.12**, absolute-norm vector chain induced by the entrywise
inverse chain. -/
theorem higham8_12_absolute_norm_vector_chain (n : ℕ)
    {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    (habs : IsAbsoluteComplexVectorNorm ν)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|)
    (z : CVec n) :
    ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
          (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ∧
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  have hZ_nonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  have hUM :
      ν (complexMatrixVecMul (complexAbsMatrix (realRectToCMatrix U_inv))
            (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) := by
    have hA :
        ∀ i j : Fin n, absMatrixRect U_inv i j ≤ M_inv i j := by
      intro i j
      simpa [absMatrixRect] using
        (higham8_12_abs_inv_le_comparison_inv n U U_inv M_inv
          hUT hU_diag hInv hM_RInv
          (inv_upper_tri n (comparisonMatrix n U) M_inv
            (by
              intro i j hij
              unfold comparisonMatrix
              simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij])
            (by
              intro i
              simp [comparisonMatrix, hU_diag i])
            (ch7_isLeftInverse_of_isRightInverse hM_RInv))) i j
    simpa [realRectToCMatrix_absMatrixRect] using
      (higham8_absolute_norm_vec_le_of_nonneg_le hν habs
        (absMatrixRect U_inv) M_inv
        (by intro i j; exact abs_nonneg _)
        hM_nonneg hA z)
  have hMW :
      ν (complexMatrixVecMul (realRectToCMatrix M_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      M_inv W_inv hM_nonneg hW_nonneg
      (higham8_12_comparisonInv_le_WInv n U M_inv W_inv
        hUT hU_diag hM_RInv hW_RInv) z
  have hWZ :
      ν (complexMatrixVecMul (realRectToCMatrix W_inv) (complexAbsVec z)) ≤
        ν (complexMatrixVecMul (realRectToCMatrix (higham8_12_ZInvFormula n α β))
          (complexAbsVec z)) :=
    higham8_absolute_norm_vec_le_of_nonneg_le hν habs
      W_inv (higham8_12_ZInvFormula n α β) hW_nonneg hZ_nonneg
      (higham8_12_WInv_le_ZInvFormula n U W_inv hU_diag hα hβ
        hα_le_diag hβ_bound hW_RInv) z
  exact ⟨hUM, hMW, hWZ⟩

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
∞-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_infNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    infNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      have habs :
          ∑ j : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ j : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_row_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow :
          (1 + β) ^ (n - 1 - i.val) ≤ (1 + β) ^ (n - 1) :=
        pow_le_pow_right₀ hbase (Nat.sub_le _ _)
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hrow := row_sum_le_infNorm (higham8_12_ZInvFormula n α β) i0
    have habs :
        ∑ j : Fin n, |higham8_12_ZInvFormula n α β i0 j| =
          ∑ j : Fin n, higham8_12_ZInvFormula n α β i0 j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact abs_of_nonneg (hnonneg i0 j)
    rw [habs, higham8_12_ZInvFormula_row_sum] at hrow
    simpa [i0] using hrow

/-- **Problem 8.5 / Theorem 8.14 support**: the scaled `Z` inverse has exact
1-norm `(1 + β)^(n-1) / α` when `α > 0` and `β ≥ 0`. -/
theorem higham8_5_ZInvFormula_oneNorm_eq (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    oneNorm (higham8_12_ZInvFormula n α β) =
      (1 / α) * (1 + β) ^ (n - 1) := by
  let jLast : Fin n := ⟨n - 1, by omega⟩
  have hnonneg := higham8_12_ZInvFormula_nonneg n hα hβ
  apply le_antisymm
  · apply oneNorm_le_of_col_sum_le
    · intro j
      have habs :
          ∑ i : Fin n, |higham8_12_ZInvFormula n α β i j| =
            ∑ i : Fin n, higham8_12_ZInvFormula n α β i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact abs_of_nonneg (hnonneg i j)
      rw [habs, higham8_12_ZInvFormula_col_sum]
      have hbase : 1 ≤ 1 + β := by linarith
      have hpow : (1 + β) ^ j.val ≤ (1 + β) ^ (n - 1) := by
        have hj : j.val ≤ n - 1 := by omega
        exact pow_le_pow_right₀ hbase hj
      exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
    · exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  · have hcol := col_sum_le_oneNorm (higham8_12_ZInvFormula n α β) jLast
    have habs :
        ∑ i : Fin n, |higham8_12_ZInvFormula n α β i jLast| =
          ∑ i : Fin n, higham8_12_ZInvFormula n α β i jLast := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact abs_of_nonneg (hnonneg i jLast)
    rw [habs, higham8_12_ZInvFormula_col_sum] at hcol
    simpa [jLast] using hcol

/-- **Problem 8.5 / Theorem 8.14 support**: the Euclidean operator norm of the
scaled `Z` inverse is bounded by the same explicit endpoint as the `1`- and
`∞`-norms. -/
theorem higham8_5_ZInvFormula_opNorm2_le (n : ℕ) (hn : 0 < n) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (1 + β) ^ (n - 1) := by
  let c : ℝ := (1 / α) * (1 + β) ^ (n - 1)
  have hbound :=
    problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf hn
      (higham8_12_ZInvFormula n α β)
  have hone := higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ
  have hinf := higham8_5_ZInvFormula_infNorm_eq n hn hα hβ
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (one_div_nonneg.mpr hα.le) (pow_nonneg (by linarith) _)
  calc
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β))
        ≤ Real.sqrt
            (oneNorm (higham8_12_ZInvFormula n α β) *
              infNorm (higham8_12_ZInvFormula n α β)) := hbound
    _ = Real.sqrt (c * c) := by rw [hone, hinf]
    _ = c := by
      rw [show c * c = c ^ 2 by ring]
      simpa [abs_of_nonneg hc_nonneg] using (Real.sqrt_sq_eq_abs c)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `1`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    oneNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_oneNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the exact `∞`-norm of the scaled
`Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_infNorm_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    infNorm (higham8_12_ZInvFormula n α β) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  rw [higham8_5_ZInvFormula_infNorm_eq n hn hα hβ]
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  exact mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)

/-- **Theorem 8.14 support**: under `β ≤ 1`, the Euclidean operator norm of
the scaled `Z` inverse is bounded by `2^(n-1) / α`. -/
theorem higham8_14_ZInvFormula_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hendpoint := higham8_5_ZInvFormula_opNorm2_le n hn hα hβ
  have hpow : (1 + β) ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) := by
    have honeβ_nonneg : 0 ≤ 1 + β := by linarith
    have honeβ_le_two : 1 + β ≤ (2 : ℝ) := by linarith
    exact pow_le_pow_left₀ honeβ_nonneg honeβ_le_two (n - 1)
  have hscale :
      (1 / α) * (1 + β) ^ (n - 1) ≤ (1 / α) * (2 : ℝ) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left hpow (one_div_nonneg.mpr hα.le)
  exact hendpoint.trans hscale

/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `1`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_oneNorm_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    oneNorm U_inv ≤ (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have honeChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact honeChain.1.trans
    (honeChain.2.1.trans
      (honeChain.2.2.trans
        (higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1)))

/-- **Theorem 8.14 support**: under `β ≤ 1`, the source `2`-norm of `U⁻¹`
is bounded by the same `Z(U)` endpoint. -/
theorem higham8_14_opNorm2_upperBound (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ) {α β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hα_le_diag : ∀ i : Fin n, α ≤ |U i i|)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    complexMatrixOp2 (realRectToCMatrix U_inv) ≤
      (1 / α) * (2 : ℝ) ^ (n - 1) := by
  have hchain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  exact hchain.1.trans
    (hchain.2.1.trans
      (hchain.2.2.trans
        (higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1)))

/-- **Algorithm 8.13**, output quantity: the comparison-inverse ∞-norm bound. -/
noncomputable def higham8_13_mu {n : ℕ} (M_inv : Fin n → Fin n → ℝ) : ℝ :=
  infNorm M_inv

/-- **Algorithm 8.13**, exact vector computed by solving `M(U)y = e`. -/
noncomputable def higham8_13_y {n : ℕ} (M_inv : Fin n → Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, M_inv i j

/-- **Algorithm 8.13**, exact recurrence for `y = M(U)⁻¹e`. -/
theorem higham8_13_comparison_inverse_row_recurrence (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_13_y M_inv i = 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U i j| * higham8_13_y M_inv j :=
  compMatrix_inv_upper_row_eq_ones n U M_inv hUT hU_diag hM_RInv i

/-- **Algorithm 8.13**, certified upper-bound property.  If `M_inv` is the
inverse of the comparison matrix and dominates `|U_inv|`, its displayed
∞-norm is an upper bound for `‖U⁻¹‖∞`. -/
theorem higham8_13_inverse_bound_from_comparison {n : ℕ}
    (U_inv M_inv : Fin n → Fin n → ℝ)
    (habs : ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j) :
    infNorm U_inv ≤ higham8_13_mu M_inv := by
  unfold higham8_13_mu
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |U_inv i j|
        ≤ ∑ j : Fin n, M_inv i j := by
          apply Finset.sum_le_sum
          intro j _
          exact habs i j
      _ = ∑ j : Fin n, |M_inv i j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact (abs_of_nonneg ((abs_nonneg (U_inv i j)).trans (habs i j))).symm
      _ ≤ infNorm M_inv := row_sum_le_infNorm M_inv i
  · exact infNorm_nonneg M_inv

/-- **Problem 8.6**, first exact vector quantity:
`M(U)⁻¹ |z|`, represented once an inverse of `M(U)` has been supplied. -/
noncomputable def higham8_6_comparisonInverseAbsVec {n : ℕ}
    (M_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, M_inv i j * |z j|

/-- **Problem 8.6**, first displayed quantity `‖M(U)⁻¹ |z|‖∞`. -/
noncomputable def higham8_6_comparisonInverseAbsVecInfNorm {n : ℕ}
    (M_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  infNormVec (higham8_6_comparisonInverseAbsVec M_inv z)

/-- **Problem 8.6**, second exact vector quantity:
`W(U)⁻¹ |z|`, represented once an inverse of `W(U)` has been supplied. -/
noncomputable def higham8_6_WInverseAbsVec {n : ℕ}
    (W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, W_inv i j * |z j|

/-- **Problem 8.6**, second displayed quantity `‖W(U)⁻¹ |z|‖∞`. -/
noncomputable def higham8_6_WInverseAbsVecInfNorm {n : ℕ}
    (W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  infNormVec (higham8_6_WInverseAbsVec W_inv z)

/-- **Problem 8.6**, backward-sweep recurrence for
`M(U)⁻¹ |z|`: the vector is computed by solving an upper-triangular
comparison-matrix system. -/
theorem higham8_6_comparisonInverseAbsVec_recurrence (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_6_comparisonInverseAbsVec M_inv z i =
      |z i| +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          |U i j| * higham8_6_comparisonInverseAbsVec M_inv z j := by
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    unfold comparisonMatrix
    simp [show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_diag : ∀ i : Fin n, comparisonMatrix n U i i ≠ 0 := by
    intro i
    simp [comparisonMatrix, hU_diag i]
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_ut := inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut hM_diag hM_LInv
  simpa [higham8_6_comparisonInverseAbsVec] using
    (compMatrix_inv_upper_row_eq n U M_inv z hUT hU_diag hM_RInv hM_inv_ut i)

/-- **Problem 8.6**, backward-sweep recurrence for
`W(U)⁻¹ |z|`: each row uses the strict-upper row maximum from `W(U)`. -/
theorem higham8_6_WInverseAbsVec_recurrence (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (i : Fin n) :
    |U i i| * higham8_6_WInverseAbsVec W_inv z i =
      |z i| +
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          higham8_12_rowMaxStrictUpper n U i *
            higham8_6_WInverseAbsVec W_inv z j := by
  let y : Fin n → ℝ := higham8_6_WInverseAbsVec W_inv z
  have hWy : ∀ i' : Fin n,
      ∑ k : Fin n, higham8_12_WMatrix n U i' k * y k = |z i'| := by
    intro i'
    simp only [y, higham8_6_WInverseAbsVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    conv_rhs =>
      rw [show |z i'| = ∑ j : Fin n, (if i' = j then 1 else 0) * |z j| by
        simp [Finset.mem_univ]]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact hW_RInv i' j
  have hrow := hWy i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  rw [higham8_12_WMatrix_diag] at hrow
  have hrest :
      ∑ k ∈ Finset.univ.erase i, higham8_12_WMatrix n U i k * y k =
        -(∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          higham8_12_rowMaxStrictUpper n U i * y j) := by
    have herase_eq :
        ∑ k ∈ Finset.univ.erase i, higham8_12_WMatrix n U i k * y k =
          ∑ k ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
            higham8_12_WMatrix n U i k * y k := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
      · intro k hk hknot
        rw [Finset.mem_erase] at hk
        have hknot' : ¬ i.val < k.val := by
          intro hc
          exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        have hlt : k.val < i.val := by omega
        rw [higham8_12_WMatrix_upper n U i k hlt, zero_mul]
    rw [herase_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [higham8_12_WMatrix_strictUpper n U hk]
    ring
  rw [hrest] at hrow
  simpa [y, higham8_6_WInverseAbsVec] using (by linarith : |U i i| * y i =
    |z i| + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
      higham8_12_rowMaxStrictUpper n U i * y j)

private theorem higham8_6_comparisonInverseAbsVec_nonneg (n : ℕ)
    (U M_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    0 ≤ higham8_6_comparisonInverseAbsVec M_inv z i := by
  have hM_nonneg :=
    higham8_12_comparisonInv_nonneg n U M_inv hUT hU_diag hM_RInv
  unfold higham8_6_comparisonInverseAbsVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM_nonneg i j) (abs_nonneg _))

private theorem higham8_6_WInverseAbsVec_nonneg (n : ℕ)
    (U W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (i : Fin n) :
    0 ≤ higham8_6_WInverseAbsVec W_inv z i := by
  have hW_nonneg :=
    higham8_12_WInv_nonneg n U W_inv hU_diag hW_RInv
  unfold higham8_6_WInverseAbsVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hW_nonneg i j) (abs_nonneg _))

/-- **Problem 8.6**, the `M(U)` bound vector is componentwise bounded by the
`W(U)` bound vector from Theorem 8.12. -/
theorem higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    ∀ i : Fin n,
      higham8_6_comparisonInverseAbsVec M_inv z i ≤
        higham8_6_WInverseAbsVec W_inv z i := by
  have hMW :=
    higham8_12_comparisonInv_le_WInv n U M_inv W_inv hUT hU_diag hM_RInv hW_RInv
  intro i
  unfold higham8_6_comparisonInverseAbsVec higham8_6_WInverseAbsVec
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hMW i j) (abs_nonneg _)

/-- **Problem 8.6**, the displayed `∞`-norm quantity obtained from `M(U)` is
bounded by the corresponding `W(U)` quantity.  The source flop counts are cost
claims; this theorem records the mathematical correctness of the two exact
triangular-solve quantities. -/
theorem higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm (n : ℕ)
    (U M_inv W_inv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv) :
    higham8_6_comparisonInverseAbsVecInfNorm M_inv z ≤
      higham8_6_WInverseAbsVecInfNorm W_inv z := by
  unfold higham8_6_comparisonInverseAbsVecInfNorm higham8_6_WInverseAbsVecInfNorm
  apply infNormVec_le_of_abs_le
  · intro i
    have hM_nonneg :=
      higham8_6_comparisonInverseAbsVec_nonneg n U M_inv z hUT hU_diag hM_RInv i
    have hW_nonneg :=
      higham8_6_WInverseAbsVec_nonneg n U W_inv z hU_diag hW_RInv i
    calc
      |higham8_6_comparisonInverseAbsVec M_inv z i|
          = higham8_6_comparisonInverseAbsVec M_inv z i :=
            abs_of_nonneg hM_nonneg
      _ ≤ higham8_6_WInverseAbsVec W_inv z i :=
            higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec n U M_inv W_inv z
              hUT hU_diag hM_RInv hW_RInv i
      _ = |higham8_6_WInverseAbsVec W_inv z i| := by
            rw [abs_of_nonneg hW_nonneg]
      _ ≤ infNormVec (higham8_6_WInverseAbsVec W_inv z) :=
            abs_le_infNormVec (higham8_6_WInverseAbsVec W_inv z) i
  · exact infNormVec_nonneg (higham8_6_WInverseAbsVec W_inv z)

/-- **Theorem 8.14**, ∞-norm lower-bound part of (8.9). -/
theorem higham8_14_infNorm_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k => |U k k|)) ≤ infNorm U_inv := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩ (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hrow :
      1 / |U k k| ≤ ∑ j : Fin n, |U_inv k j| :=
    triInv_row_sum_lowerBound n U U_inv hDD.1 hDD.2.1 hInv k
  calc
    1 / α = 1 / |U k k| := by
      simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
    _ ≤ ∑ j : Fin n, |U_inv k j| := hrow
    _ ≤ infNorm U_inv := row_sum_le_infNorm U_inv k

/-- **Theorem 8.14**, `1`-norm lower-bound part of (8.9) at a chosen
diagonal index. -/
theorem higham8_14_oneNorm_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    (1 / |U i0 i0|) ≤ oneNorm U_inv := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag : U_inv i0 i0 = 1 / U i0 i0 :=
    inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut i0
  have hterm : |U_inv i0 i0| ≤ ∑ i : Fin n, |U_inv i i0| := by
    simpa using
      (Finset.single_le_sum (fun i _hi => abs_nonneg (U_inv i i0))
        (Finset.mem_univ i0))
  have habs : |U_inv i0 i0| = 1 / |U i0 i0| := by
    rw [hdiag, abs_div, abs_one]
  calc
    1 / |U i0 i0| = |U_inv i0 i0| := by rw [habs]
    _ ≤ ∑ i : Fin n, |U_inv i i0| := hterm
    _ ≤ oneNorm U_inv := col_sum_le_oneNorm U_inv i0

/-- **Theorem 8.14**, `2`-norm lower-bound part of (8.9) at a chosen
diagonal index. -/
theorem higham8_14_opNorm2_lowerBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv) :
    (1 / |U i0 i0|) ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := by
  have hInv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hdiag : U_inv i0 i0 = 1 / U i0 i0 :=
    inv_diag_entry n U U_inv hUT hU_diag hInv.1 hInv_ut i0
  have hbound :=
    hasComplexMatrixLpBound_apply
      (complexMatrixOp2_hasComplexMatrixLpBound (realRectToCMatrix U_inv))
      (standardBasisCVec i0)
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hcol :
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) ≤
        complexMatrixOp2 (realRectToCMatrix U_inv) := by
    rw [complexMatrixVecMul_standardBasisCVec,
      complexVecLpNorm_standardBasisCVec (ENNReal.ofReal (2 : ℝ)) i0, mul_one] at hbound
    exact hbound
  have hcoord :
      ‖realRectToCMatrix U_inv i0 i0‖ ≤
        complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) := by
    letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    simpa using
      (complexVecLpNorm_coord_le (ENNReal.ofReal (2 : ℝ))
        (fun i : Fin n => realRectToCMatrix U_inv i i0) i0)
  calc
    1 / |U i0 i0| = |U_inv i0 i0| := by
      rw [hdiag, abs_div, abs_one]
    _ = ‖realRectToCMatrix U_inv i0 i0‖ := by
      simp [realRectToCMatrix]
    _ ≤ complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin n => realRectToCMatrix U_inv i i0) := hcoord
    _ ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := hcol

/-- **Theorem 8.14**, ∞-norm part of the inverse-bound chain under (8.5). -/
theorem higham8_14_infNorm_upperBound (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n)
    (hDD : IsDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    infNorm U_inv ≤
      2 ^ (n - 1) *
        (1 / Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
          (fun k => |U k k|)) :=
  triInv_infNorm_upperBound n U U_inv i0 hDD hInv

/-- **Theorem 8.14**, packaged `∞/1/2` norm chains in the source notation
using the minimum diagonal magnitude. -/
theorem higham8_14_full_norm_chain (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv W_inv : Fin n → Fin n → ℝ)
    (i0 : Fin n) {β : ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hW_RInv : IsRightInverse n (higham8_12_WMatrix n U) W_inv)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ_bound : ∀ i j : Fin n, i.val < j.val → |U i j| ≤ β * |U i i|) :
    let α : ℝ :=
      Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
        (fun k : Fin n => |U k k|)
    (1 / α ≤ infNorm U_inv ∧
        infNorm U_inv ≤ infNorm M_inv ∧
        infNorm M_inv ≤ infNorm W_inv ∧
        infNorm W_inv ≤ infNorm (higham8_12_ZInvFormula n α β) ∧
        infNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ oneNorm U_inv ∧
        oneNorm U_inv ≤ oneNorm M_inv ∧
        oneNorm M_inv ≤ oneNorm W_inv ∧
        oneNorm W_inv ≤ oneNorm (higham8_12_ZInvFormula n α β) ∧
        oneNorm (higham8_12_ZInvFormula n α β) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) ∧
      (1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) ∧
        complexMatrixOp2 (realRectToCMatrix U_inv) ≤
          complexMatrixOp2 (realRectToCMatrix M_inv) ∧
        complexMatrixOp2 (realRectToCMatrix M_inv) ≤
          complexMatrixOp2 (realRectToCMatrix W_inv) ∧
        complexMatrixOp2 (realRectToCMatrix W_inv) ≤
          complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ∧
        complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
          (1 / α) * (2 : ℝ) ^ (n - 1)) := by
  classical
  let α : ℝ :=
    Finset.inf' Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|)
  rcases Finset.exists_mem_eq_inf'
      (s := Finset.univ) ⟨i0, Finset.mem_univ i0⟩
      (fun k : Fin n => |U k k|) with
    ⟨k, _hk_mem, hα_eq⟩
  have hα : 0 < α := by
    dsimp [α]
    rw [hα_eq]
    exact abs_pos.mpr (hU_diag k)
  have hα_le_diag : ∀ i : Fin n, α ≤ |U i i| := by
    intro i
    simpa [α] using
      (Finset.inf'_le (s := Finset.univ)
        (f := fun k : Fin n => |U k k|) (b := i) (Finset.mem_univ i))
  have hDD : IsDiagDominantUpper n U := by
    refine ⟨hUT, hU_diag, ?_⟩
    intro i j hij
    have hdiag_nonneg : 0 ≤ |U i i| := abs_nonneg (U i i)
    calc
      |U i j| ≤ β * |U i i| := hβ_bound i j hij
      _ ≤ |U i i| := by nlinarith
  have hInfChain :=
    higham8_12_infNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOneChain :=
    higham8_12_oneNorm_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hOp2Chain :=
    higham8_12_opNorm2_chain n U U_inv M_inv W_inv
      hUT hU_diag hInv hM_RInv hW_RInv hα hβ hα_le_diag hβ_bound
  have hInfLower :
      1 / α ≤ infNorm U_inv :=
    higham8_14_infNorm_lowerBound n U U_inv i0 hDD hInv
  have hOneLower :
      1 / α ≤ oneNorm U_inv := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ oneNorm U_inv :=
        higham8_14_oneNorm_lowerBound n U U_inv k hUT hU_diag hInv
  have hOp2Lower :
      1 / α ≤ complexMatrixOp2 (realRectToCMatrix U_inv) := by
    calc
      1 / α = 1 / |U k k| := by
        simpa [α] using congrArg (fun x : ℝ => 1 / x) hα_eq
      _ ≤ complexMatrixOp2 (realRectToCMatrix U_inv) :=
        higham8_14_opNorm2_lowerBound n U U_inv k hUT hU_diag hInv
  have hInfUpperZ :
      infNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_infNorm_upperBound n hn hα hβ hβ1
  have hOneUpperZ :
      oneNorm (higham8_12_ZInvFormula n α β) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_oneNorm_upperBound n hn hα hβ hβ1
  have hOp2UpperZ :
      complexMatrixOp2 (realRectToCMatrix (higham8_12_ZInvFormula n α β)) ≤
        (1 / α) * (2 : ℝ) ^ (n - 1) :=
    higham8_14_ZInvFormula_opNorm2_upperBound n hn hα hβ hβ1
  exact ⟨⟨hInfLower, hInfChain.1, hInfChain.2.1, hInfChain.2.2, hInfUpperZ⟩,
    ⟨⟨hOneLower, hOneChain.1, hOneChain.2.1, hOneChain.2.2, hOneUpperZ⟩,
      ⟨hOp2Lower, hOp2Chain.1, hOp2Chain.2.1, hOp2Chain.2.2, hOp2UpperZ⟩⟩⟩

/-! ## §8.4 Parallel fan-in exact product surface -/

/-- **Equation (8.12)**: the `k`th lower-triangular column factor `L_k`.
It is the identity matrix except that column `k` is copied from `L`. -/
noncomputable def higham8_12_lowerColumnFactor (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i j =>
    if j = k then L i k
    else if i = j then 1 else 0

/-- Prefix product of the first `r` factors in the exact factorization
`L = L_1 ... L_n` from (8.12). -/
noncomputable def higham8_12_lowerColumnProductPrefix (n : ℕ)
    (L : Fin n → Fin n → ℝ) : (r : ℕ) → r ≤ n → Fin n → Fin n → ℝ
  | 0, _ => idMatrix n
  | r + 1, hr =>
      matMul n (higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr))
        (higham8_12_lowerColumnFactor n L ⟨r, hr⟩)

/-- Full exact product of the column factors in (8.12). -/
noncomputable def higham8_12_lowerColumnProduct (n : ℕ)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham8_12_lowerColumnProductPrefix n L n (le_refl n)

/-- Prefix invariant for the exact column-factor product: after multiplying the
first `r` factors, the first `r` columns agree with `L` and the remaining
columns are still those of the identity. -/
theorem higham8_12_lowerColumnProductPrefix_apply (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0) :
    ∀ (r : ℕ) (hr : r ≤ n) (i j : Fin n),
      higham8_12_lowerColumnProductPrefix n L r hr i j =
        if j.val < r then L i j else idMatrix n i j := by
  intro r
  induction r with
  | zero =>
      intro hr i j
      simp [higham8_12_lowerColumnProductPrefix]
  | succ r ih =>
      intro hr i j
      have hri : r < n := hr
      unfold higham8_12_lowerColumnProductPrefix
      unfold matMul
      by_cases hjr : j.val = r
      · have hj_eq_col : j = (⟨r, hr⟩ : Fin n) := Fin.ext hjr
        have hsum :
            (∑ k : Fin n,
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i k *
                higham8_12_lowerColumnFactor n L ⟨r, hr⟩ k j) =
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i i *
                higham8_12_lowerColumnFactor n L ⟨r, hr⟩ i j := by
          apply Finset.sum_eq_single i
          · intro k _ hk
            by_cases hkr : k.val < r
            · have hLkr : L k (⟨r, hr⟩ : Fin n) = 0 := hLT k ⟨r, hr⟩ hkr
              rw [ih (Nat.le_of_succ_le hr) i k]
              simp [higham8_12_lowerColumnFactor, hj_eq_col, hkr, hLkr]
            · have hik : i ≠ k := by exact Ne.symm hk
              rw [ih (Nat.le_of_succ_le hr) i k]
              simp [higham8_12_lowerColumnFactor, hj_eq_col, hkr, hik, idMatrix]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
        rw [hsum]
        rw [ih (Nat.le_of_succ_le hr) i i]
        by_cases hir : i.val < r
        · have hLij : L i (⟨r, hr⟩ : Fin n) = 0 := hLT i ⟨r, hr⟩ hir
          simp [higham8_12_lowerColumnFactor, hj_eq_col, hir, hLij]
        · simp [higham8_12_lowerColumnFactor, hj_eq_col, hir, idMatrix]
      · by_cases hjlt : j.val < r
        ·
          have hj_ne_col : j ≠ (⟨r, hr⟩ : Fin n) := by
            intro h
            exact hjr (congrArg Fin.val h)
          have hfactor_j :
              higham8_12_lowerColumnFactor n L ⟨r, hr⟩ j j = 1 := by
            simp [higham8_12_lowerColumnFactor, hj_ne_col]
          have hsum :
            (∑ k : Fin n,
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i k *
                higham8_12_lowerColumnFactor n L ⟨r, hr⟩ k j) =
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j := by
            calc
              (∑ k : Fin n,
                higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i k *
                  higham8_12_lowerColumnFactor n L ⟨r, hr⟩ k j)
                  =
                higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j *
                  higham8_12_lowerColumnFactor n L ⟨r, hr⟩ j j := by
                    apply Finset.sum_eq_single j
                    · intro k _ hk
                      have hkj : k ≠ j := hk
                      rw [ih (Nat.le_of_succ_le hr) i k]
                      by_cases hkr : k.val < r
                      · simp [higham8_12_lowerColumnFactor, hj_ne_col, hkj, hkr]
                      · simp [higham8_12_lowerColumnFactor, hj_ne_col, hkj, hkr]
                    · intro hj
                      exact (hj (Finset.mem_univ j)).elim
              _ = higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j := by
                    rw [hfactor_j, mul_one]
          rw [hsum, ih (Nat.le_of_succ_le hr) i j]
          simp [hjlt, Nat.lt_trans hjlt (Nat.lt_succ_self r)]
        ·
          have hjgt : r < j.val := by omega
          have hj_ne_col : j ≠ (⟨r, hr⟩ : Fin n) := by
            intro h
            exact hjr (congrArg Fin.val h)
          have hfactor_j :
              higham8_12_lowerColumnFactor n L ⟨r, hr⟩ j j = 1 := by
            simp [higham8_12_lowerColumnFactor, hj_ne_col]
          have hsum :
            (∑ k : Fin n,
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i k *
                higham8_12_lowerColumnFactor n L ⟨r, hr⟩ k j) =
              higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j := by
            calc
              (∑ k : Fin n,
                higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i k *
                  higham8_12_lowerColumnFactor n L ⟨r, hr⟩ k j)
                  =
                higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j *
                  higham8_12_lowerColumnFactor n L ⟨r, hr⟩ j j := by
                    apply Finset.sum_eq_single j
                    · intro k _ hk
                      have hkj : k ≠ j := hk
                      rw [ih (Nat.le_of_succ_le hr) i k]
                      by_cases hkr : k.val < r
                      · simp [higham8_12_lowerColumnFactor, hj_ne_col, hkj, hkr]
                      · simp [higham8_12_lowerColumnFactor, hj_ne_col, hkj, hkr]
                    · intro hj
                      exact (hj (Finset.mem_univ j)).elim
              _ = higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr) i j := by
                    rw [hfactor_j, mul_one]
          rw [hsum, ih (Nat.le_of_succ_le hr) i j]
          have hjnotr : ¬ j.val < r := by omega
          have hjnotrs : ¬ j.val < r + 1 := by omega
          simp [hjnotr, hjnotrs]

/-- **Equation (8.12)** exact factorization: every lower-triangular matrix is the
product of its column factors `L_1 ... L_n`. -/
theorem higham8_12_lowerColumnProduct_eq (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0) :
    higham8_12_lowerColumnProduct n L = L := by
  ext i j
  unfold higham8_12_lowerColumnProduct
  rw [higham8_12_lowerColumnProductPrefix_apply n L hLT n (le_refl n) i j]
  have hj : j.val < n := j.isLt
  simp [hj]

/-- **Equation (8.13)**: the exact inverse `M_k = L_k⁻¹` of a lower-column
factor.  Outside column `k` it is the identity; column `k` is divided by the
diagonal pivot and its strict-lower entries change sign. -/
noncomputable def higham8_13_lowerColumnInverseFactor (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i j =>
    if j = k then
      if i = k then 1 / L k k else -(L i k) / L k k
    else if i = j then 1 else 0

/-- The displayed `M_k` is a right inverse of the source column factor `L_k`.
This is the first exact bridge needed by the fan-in argument; no rounded or
target-scale hypothesis is used. -/
theorem higham8_13_lowerColumnFactor_mul_inverseFactor (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) (hkk : L k k ≠ 0) :
    matMul n (higham8_12_lowerColumnFactor n L k)
        (higham8_13_lowerColumnInverseFactor n L k) = idMatrix n := by
  funext i j
  unfold matMul
  by_cases hj : j = k
  · subst j
    by_cases hi : i = k
    · subst i
      rw [Finset.sum_eq_single k]
      · simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hkk, idMatrix]
      · intro r _ hr
        simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hr, Ne.symm hr]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    · rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) k
          (fun r : Fin n =>
            higham8_12_lowerColumnFactor n L k i r *
              higham8_13_lowerColumnInverseFactor n L k r k) (by simp)]
      rw [Finset.sum_eq_single i]
      · simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hi, idMatrix]
        field_simp
        ring
      · intro r hr hri
        have hrk : r ≠ k := by simpa using hr
        simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hrk, Ne.symm hri]
      · intro hi_mem
        exact (hi_mem (by simp [hi])).elim
  · rw [Finset.sum_eq_single j]
    · simp [higham8_12_lowerColumnFactor,
        higham8_13_lowerColumnInverseFactor, hj, idMatrix]
    · intro r _ hr
      simp [higham8_13_lowerColumnInverseFactor, hj, hr]
    · intro hj_mem
      exact (hj_mem (Finset.mem_univ j)).elim

/-- The displayed `M_k` is also a left inverse of `L_k`; hence it is the
genuine two-sided inverse used in (8.13). -/
theorem higham8_13_inverseFactor_mul_lowerColumnFactor (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) (hkk : L k k ≠ 0) :
    matMul n (higham8_13_lowerColumnInverseFactor n L k)
        (higham8_12_lowerColumnFactor n L k) = idMatrix n := by
  funext i j
  unfold matMul
  by_cases hj : j = k
  · subst j
    by_cases hi : i = k
    · subst i
      rw [Finset.sum_eq_single k]
      · simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hkk, idMatrix]
      · intro r _ hr
        simp [higham8_13_lowerColumnInverseFactor, hr, Ne.symm hr]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    · rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) k
          (fun r : Fin n =>
            higham8_13_lowerColumnInverseFactor n L k i r *
              higham8_12_lowerColumnFactor n L k r k) (by simp)]
      rw [Finset.sum_eq_single i]
      · simp [higham8_12_lowerColumnFactor,
          higham8_13_lowerColumnInverseFactor, hi, hkk, idMatrix]
      · intro r hr hri
        have hrk : r ≠ k := by simpa using hr
        simp [higham8_13_lowerColumnInverseFactor, hrk, Ne.symm hri]
      · intro hi_mem
        exact (hi_mem (by simp [hi])).elim
  · rw [Finset.sum_eq_single j]
    · simp [higham8_12_lowerColumnFactor,
        higham8_13_lowerColumnInverseFactor, hj, idMatrix]
    · intro r _ hr
      simp [higham8_12_lowerColumnFactor, hj, hr]
    · intro hj_mem
      exact (hj_mem (Finset.mem_univ j)).elim

/-- `L_k` and the explicit `M_k` form an exact two-sided inverse pair. -/
theorem higham8_13_lowerColumnFactor_inverse (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) (hkk : L k k ≠ 0) :
    IsInverse n (higham8_12_lowerColumnFactor n L k)
      (higham8_13_lowerColumnInverseFactor n L k) := by
  constructor
  · intro i j
    simpa [matMul, idMatrix] using congrFun₂
      (higham8_13_inverseFactor_mul_lowerColumnFactor n L k hkk) i j
  · intro i j
    simpa [matMul, idMatrix] using congrFun₂
      (higham8_13_lowerColumnFactor_mul_inverseFactor n L k hkk) i j

/-- Taking entrywise absolute values of `M_k` is exactly the inverse column
factor associated with the comparison matrix `M(L)`. -/
theorem higham8_13_abs_lowerColumnInverseFactor (n : ℕ)
    (L : Fin n → Fin n → ℝ) (k : Fin n) :
    absMatrix n (higham8_13_lowerColumnInverseFactor n L k) =
      higham8_13_lowerColumnInverseFactor n (comparisonMatrix n L) k := by
  funext i j
  by_cases hj : j = k
  · subst j
    by_cases hi : i = k
    · subst i
      simp [absMatrix, higham8_13_lowerColumnInverseFactor,
        comparisonMatrix]
    · simp [absMatrix, higham8_13_lowerColumnInverseFactor,
        comparisonMatrix, hi, abs_div]
  · by_cases hij : i = j
    · subst i
      simp [absMatrix, higham8_13_lowerColumnInverseFactor, hj]
    · simp [absMatrix, higham8_13_lowerColumnInverseFactor, hj, hij]

/-- Reverse prefix product `M_r ⋯ M_1` of the exact inverse column factors.
This is the exact-arithmetic product evaluated by the fan-in tree. -/
noncomputable def higham8_13_inverseColumnProductPrefix (n : ℕ)
    (L : Fin n → Fin n → ℝ) :
    (r : ℕ) → r ≤ n → Fin n → Fin n → ℝ
  | 0, _ => idMatrix n
  | r + 1, hr =>
      matMul n (higham8_13_lowerColumnInverseFactor n L ⟨r, hr⟩)
        (higham8_13_inverseColumnProductPrefix n L r (Nat.le_of_succ_le hr))

/-- Full reverse product `M_n ⋯ M_1`. -/
noncomputable def higham8_13_inverseColumnProduct (n : ℕ)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham8_13_inverseColumnProductPrefix n L n (le_refl n)

/-- Every exact lower-column prefix times the matching reverse inverse prefix
is the identity. -/
theorem higham8_13_lowerColumnProductPrefix_mul_inversePrefix (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hdiag : ∀ k : Fin n, L k k ≠ 0) :
    ∀ (r : ℕ) (hr : r ≤ n),
      matMul n (higham8_12_lowerColumnProductPrefix n L r hr)
          (higham8_13_inverseColumnProductPrefix n L r hr) = idMatrix n := by
  intro r
  induction r with
  | zero =>
      intro hr
      simp [higham8_12_lowerColumnProductPrefix,
        higham8_13_inverseColumnProductPrefix, matMul_id_left]
  | succ r ih =>
      intro hr
      unfold higham8_12_lowerColumnProductPrefix
      unfold higham8_13_inverseColumnProductPrefix
      rw [matMul_assoc]
      rw [← matMul_assoc n
        (higham8_12_lowerColumnFactor n L ⟨r, hr⟩)
        (higham8_13_lowerColumnInverseFactor n L ⟨r, hr⟩)]
      rw [higham8_13_lowerColumnFactor_mul_inverseFactor n L ⟨r, hr⟩
        (hdiag ⟨r, hr⟩)]
      rw [matMul_id_left]
      exact ih (Nat.le_of_succ_le hr)

/-- Conversely, each reverse inverse prefix times its lower-column prefix is
the identity. -/
theorem higham8_13_inversePrefix_mul_lowerColumnProductPrefix (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hdiag : ∀ k : Fin n, L k k ≠ 0) :
    ∀ (r : ℕ) (hr : r ≤ n),
      matMul n (higham8_13_inverseColumnProductPrefix n L r hr)
          (higham8_12_lowerColumnProductPrefix n L r hr) = idMatrix n := by
  intro r
  induction r with
  | zero =>
      intro hr
      simp [higham8_12_lowerColumnProductPrefix,
        higham8_13_inverseColumnProductPrefix, matMul_id_left]
  | succ r ih =>
      intro hr
      unfold higham8_12_lowerColumnProductPrefix
      unfold higham8_13_inverseColumnProductPrefix
      rw [matMul_assoc]
      rw [← matMul_assoc n
        (higham8_13_inverseColumnProductPrefix n L r (Nat.le_of_succ_le hr))
        (higham8_12_lowerColumnProductPrefix n L r (Nat.le_of_succ_le hr))]
      rw [ih (Nat.le_of_succ_le hr)]
      rw [matMul_id_left]
      exact higham8_13_inverseFactor_mul_lowerColumnFactor n L ⟨r, hr⟩
        (hdiag ⟨r, hr⟩)

/-- The reverse product of the `M_k` factors is a two-sided inverse of `L`.
This discharges the exact `M_i=L_i⁻¹` producer/solve bridge in (8.13). -/
theorem higham8_13_inverseColumnProduct_inverse (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hdiag : ∀ k : Fin n, L k k ≠ 0) :
    IsInverse n L (higham8_13_inverseColumnProduct n L) := by
  have hprod : higham8_12_lowerColumnProduct n L = L :=
    higham8_12_lowerColumnProduct_eq n L hLT
  have hleft := higham8_13_inversePrefix_mul_lowerColumnProductPrefix
    n L hdiag n (le_refl n)
  have hright := higham8_13_lowerColumnProductPrefix_mul_inversePrefix
    n L hdiag n (le_refl n)
  change matMul n (higham8_13_inverseColumnProduct n L)
    (higham8_12_lowerColumnProduct n L) = idMatrix n at hleft
  change matMul n (higham8_12_lowerColumnProduct n L)
    (higham8_13_inverseColumnProduct n L) = idMatrix n at hright
  rw [hprod] at hleft hright
  constructor
  · intro i j
    simpa [matMul, idMatrix] using congrFun₂ hleft i j
  · intro i j
    simpa [matMul, idMatrix] using congrFun₂ hright i j

/-- A left inverse and a right inverse of the same finite square matrix agree.
Kept local to the Chapter-8 surface so the inverse-column-factor bridge does
not depend on a later chapter. -/
theorem higham8_13_leftInverse_eq_rightInverse {n : ℕ}
    (A X Y : Fin n → Fin n → ℝ)
    (hX : IsLeftInverse n A X) (hY : IsRightInverse n A Y) : X = Y := by
  have hXA : matMul n X A = idMatrix n := by
    funext i j
    exact hX i j
  have hAY : matMul n A Y = idMatrix n := by
    funext i j
    exact hY i j
  calc
    X = matMul n X (idMatrix n) := (matMul_id_right n X).symm
    _ = matMul n X (matMul n A Y) := by rw [hAY]
    _ = matMul n (matMul n X A) Y := (matMul_assoc n X A Y).symm
    _ = matMul n (idMatrix n) Y := by rw [hXA]
    _ = Y := matMul_id_left n Y

/-- **Equation (8.13)**, source's displayed `n = 7` fan-in matrix product
shape before rounding errors are introduced. -/
noncomputable def higham8_13_fanIn7Matrix (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n
    (matMul n (matMul n M7 M6) (matMul n M5 M4))
    (matMul n (matMul n M3 M2) M1)

/-- **Equation (8.13)**, applying the displayed `n = 7` fan-in product to the
right-hand side vector. -/
noncomputable def higham8_13_fanIn7Apply (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    Fin n → ℝ :=
  matMulVec n (higham8_13_fanIn7Matrix n M1 M2 M3 M4 M5 M6 M7) b

/-- Left-associated reference product for the same seven matrices. -/
noncomputable def higham8_13_sequential7Matrix (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n
    (matMul n
      (matMul n
        (matMul n
          (matMul n (matMul n M7 M6) M5) M4) M3) M2) M1

/-- **Equation (8.13)** exact-arithmetic support: the displayed fan-in tree is
only a parenthesization of the same exact matrix product.  The rounded fan-in
expansion and residual bounds `(8.14)`--`(8.20)` remain separate rounding rows. -/
theorem higham8_13_fanIn7Matrix_eq_sequential7Matrix (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) :
    higham8_13_fanIn7Matrix n M1 M2 M3 M4 M5 M6 M7 =
      higham8_13_sequential7Matrix n M1 M2 M3 M4 M5 M6 M7 := by
  unfold higham8_13_fanIn7Matrix higham8_13_sequential7Matrix
  rw [← matMul_assoc n (matMul n (matMul n M7 M6) (matMul n M5 M4))
    (matMul n M3 M2) M1]
  rw [← matMul_assoc n (matMul n (matMul n M7 M6) (matMul n M5 M4)) M3 M2]
  rw [← matMul_assoc n (matMul n M7 M6) M5 M4]

/-- For seven source column factors, the balanced fan-in parenthesization is
exactly the full reverse inverse-column product `M₇⋯M₁`. -/
theorem higham8_13_fanIn7InverseMatrix_eq
    (L : Fin 7 → Fin 7 → ℝ) :
    higham8_13_fanIn7Matrix 7
        (higham8_13_lowerColumnInverseFactor 7 L 0)
        (higham8_13_lowerColumnInverseFactor 7 L 1)
        (higham8_13_lowerColumnInverseFactor 7 L 2)
        (higham8_13_lowerColumnInverseFactor 7 L 3)
        (higham8_13_lowerColumnInverseFactor 7 L 4)
        (higham8_13_lowerColumnInverseFactor 7 L 5)
        (higham8_13_lowerColumnInverseFactor 7 L 6) =
      higham8_13_inverseColumnProduct 7 L := by
  simp [higham8_13_fanIn7Matrix, higham8_13_inverseColumnProduct,
    higham8_13_inverseColumnProductPrefix, matMul_assoc, matMul_id_right]

/-- The exact seven-factor fan-in application genuinely solves `Lx=b`; the
former free `hsolve` premise is produced from the source lower-triangular and
nonsingular-diagonal hypotheses. -/
theorem higham8_13_fanIn7InverseApply_solves
    (L : Fin 7 → Fin 7 → ℝ) (b : Fin 7 → ℝ)
    (hLT : ∀ i j : Fin 7, i.val < j.val → L i j = 0)
    (hdiag : ∀ k : Fin 7, L k k ≠ 0) :
    matMulVec 7 L
        (higham8_13_fanIn7Apply 7
          (higham8_13_lowerColumnInverseFactor 7 L 0)
          (higham8_13_lowerColumnInverseFactor 7 L 1)
          (higham8_13_lowerColumnInverseFactor 7 L 2)
          (higham8_13_lowerColumnInverseFactor 7 L 3)
          (higham8_13_lowerColumnInverseFactor 7 L 4)
          (higham8_13_lowerColumnInverseFactor 7 L 5)
          (higham8_13_lowerColumnInverseFactor 7 L 6) b) = b := by
  have hInv := higham8_13_inverseColumnProduct_inverse 7 L hLT hdiag
  have hmat :
      matMul 7 L
          (higham8_13_fanIn7Matrix 7
            (higham8_13_lowerColumnInverseFactor 7 L 0)
            (higham8_13_lowerColumnInverseFactor 7 L 1)
            (higham8_13_lowerColumnInverseFactor 7 L 2)
            (higham8_13_lowerColumnInverseFactor 7 L 3)
            (higham8_13_lowerColumnInverseFactor 7 L 4)
            (higham8_13_lowerColumnInverseFactor 7 L 5)
            (higham8_13_lowerColumnInverseFactor 7 L 6)) = idMatrix 7 := by
    rw [higham8_13_fanIn7InverseMatrix_eq]
    funext i j
    exact hInv.2 i j
  ext i
  unfold higham8_13_fanIn7Apply
  rw [← matMulVec_matMul 7 L
    (higham8_13_fanIn7Matrix 7
      (higham8_13_lowerColumnInverseFactor 7 L 0)
      (higham8_13_lowerColumnInverseFactor 7 L 1)
      (higham8_13_lowerColumnInverseFactor 7 L 2)
      (higham8_13_lowerColumnInverseFactor 7 L 3)
      (higham8_13_lowerColumnInverseFactor 7 L 4)
      (higham8_13_lowerColumnInverseFactor 7 L 5)
      (higham8_13_lowerColumnInverseFactor 7 L 6)) b i]
  rw [hmat, matMulVec_id]

/-- **Equation (8.14)**, rounded `n = 7` fan-in matrix expression.

The displayed first-order analysis writes the computed tree in terms of
perturbations of the local matrix products.  This definition records the exact
algebraic expression before bounding the perturbation matrices. -/
noncomputable def higham8_14_fanIn7RoundedMatrix (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 :
      Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n
    (fun i j =>
      matMul n
        (fun i j => matMul n M7 M6 i j + Δ76 i j)
        (fun i j => matMul n M5 M4 i j + Δ54 i j) i j +
        Δ7654 i j)
    (matMul n
      (fun i j => matMul n M3 M2 i j + Δ32 i j)
      (fun i j => M1 i j + Δ1 i j))

/-- **Equation (8.14)**, rounded `n = 7` fan-in expression applied to the
right-hand side vector. -/
noncomputable def higham8_14_fanIn7RoundedApply (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 :
      Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  matMulVec n
    (higham8_14_fanIn7RoundedMatrix n
      M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654)
    b

/-- The literal rounded fan-in executor underlying the source's displayed
`n = 7` tree.  Matrix products at the four internal matrix nodes and all three
matrix-vector actions are evaluated by the repository floating-point model. -/
noncomputable def higham8_14_fanIn7Executor (fp : FPModel) (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    Fin n → ℝ :=
  let C76 := fl_matMul fp n n n M7 M6
  let C54 := fl_matMul fp n n n M5 M4
  let C7654 := fl_matMul fp n n n C76 C54
  let C32 := fl_matMul fp n n n M3 M2
  let v1 := fl_matVec fp n n M1 b
  let v321 := fl_matVec fp n n C32 v1
  fl_matVec fp n n C7654 v321

/-- **Equation (8.14), producer bridge.**  The literal rounded fan-in executor
has exactly the source's perturbation-tree form.  In addition to constructing
all five perturbations, the theorem exposes certified local envelopes.  The
two composite envelopes retain the harmless higher-order terms explicitly:
the matrix-product residual plus the backward error of the subsequent
matrix-vector action.

This theorem removes the former gap between the symbolic `(8.14)` expression
and an actual sequence of `fl_matMul`/`fl_matVec` operations. -/
theorem higham8_14_fanIn7Executor_eq_roundedApply (fp : FPModel) (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ Δ1 Δ32 Δ54 Δ76 Δ7654 : Fin n → Fin n → ℝ,
      higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b =
        higham8_14_fanIn7RoundedApply n
          M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 b ∧
      (∀ i j, |Δ1 i j| ≤ gamma fp n * |M1 i j|) ∧
      (∀ i j,
        |Δ32 i j| ≤
          gamma fp n * (∑ k : Fin n, |M3 i k| * |M2 k j|) +
            gamma fp n * |fl_matMul fp n n n M3 M2 i j|) ∧
      (∀ i j,
        |Δ54 i j| ≤ gamma fp n * (∑ k : Fin n, |M5 i k| * |M4 k j|)) ∧
      (∀ i j,
        |Δ76 i j| ≤ gamma fp n * (∑ k : Fin n, |M7 i k| * |M6 k j|)) ∧
      (∀ i j,
        |Δ7654 i j| ≤
          gamma fp n *
              (∑ k : Fin n,
                |fl_matMul fp n n n M7 M6 i k| *
                  |fl_matMul fp n n n M5 M4 k j|) +
            gamma fp n *
              |fl_matMul fp n n n
                (fl_matMul fp n n n M7 M6)
                (fl_matMul fp n n n M5 M4) i j|) := by
  let C76 : Fin n → Fin n → ℝ := fl_matMul fp n n n M7 M6
  let C54 : Fin n → Fin n → ℝ := fl_matMul fp n n n M5 M4
  let C7654 : Fin n → Fin n → ℝ := fl_matMul fp n n n C76 C54
  let C32 : Fin n → Fin n → ℝ := fl_matMul fp n n n M3 M2
  let v1 : Fin n → ℝ := fl_matVec fp n n M1 b
  let v321 : Fin n → ℝ := fl_matVec fp n n C32 v1
  let xhat : Fin n → ℝ := fl_matVec fp n n C7654 v321
  obtain ⟨Δ1, hΔ1, hv1⟩ := matVec_backward_error fp n n M1 b hn
  obtain ⟨E32, hE32, hv321⟩ := matVec_backward_error fp n n C32 v1 hn
  obtain ⟨E7654, hE7654, hxhat⟩ :=
    matVec_backward_error fp n n C7654 v321 hn
  let Δ76 : Fin n → Fin n → ℝ := fun i j => C76 i j - matMul n M7 M6 i j
  let Δ54 : Fin n → Fin n → ℝ := fun i j => C54 i j - matMul n M5 M4 i j
  let Δ32 : Fin n → Fin n → ℝ :=
    fun i j => C32 i j - matMul n M3 M2 i j + E32 i j
  let Δ7654 : Fin n → Fin n → ℝ :=
    fun i j => C7654 i j - matMul n C76 C54 i j + E7654 i j
  have hv1' : v1 = matMulVec n (fun i j => M1 i j + Δ1 i j) b := by
    ext i
    simpa [v1, matMulVec] using hv1 i
  have hv321' : v321 = matMulVec n (fun i j => C32 i j + E32 i j) v1 := by
    ext i
    simpa [v321, matMulVec] using hv321 i
  have hxhat' : xhat = matMulVec n (fun i j => C7654 i j + E7654 i j) v321 := by
    ext i
    simpa [xhat, matMulVec] using hxhat i
  have h76 : (fun i j => matMul n M7 M6 i j + Δ76 i j) = C76 := by
    funext i j
    simp [Δ76]
  have h54 : (fun i j => matMul n M5 M4 i j + Δ54 i j) = C54 := by
    funext i j
    simp [Δ54]
  have h32 :
      (fun i j => matMul n M3 M2 i j + Δ32 i j) =
        (fun i j => C32 i j + E32 i j) := by
    funext i j
    dsimp [Δ32]
    ring
  have h7654 :
      (fun i j => matMul n C76 C54 i j + Δ7654 i j) =
        (fun i j => C7654 i j + E7654 i j) := by
    funext i j
    dsimp [Δ7654]
    ring
  refine ⟨Δ1, Δ32, Δ54, Δ76, Δ7654, ?_, hΔ1, ?_, ?_, ?_, ?_⟩
  · calc
      higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b = xhat := rfl
      _ = matMulVec n (fun i j => C7654 i j + E7654 i j) v321 := hxhat'
      _ = matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j) v321 := by
        rw [h7654]
      _ = matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
            (matMulVec n (fun i j => C32 i j + E32 i j) v1) := by
        rw [hv321']
      _ = matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
            (matMulVec n (fun i j => matMul n M3 M2 i j + Δ32 i j) v1) := by
        rw [h32]
      _ = matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
            (matMulVec n (fun i j => matMul n M3 M2 i j + Δ32 i j)
              (matMulVec n (fun i j => M1 i j + Δ1 i j) b)) := by
        rw [hv1']
      _ = higham8_14_fanIn7RoundedApply n
            M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 b := by
        unfold higham8_14_fanIn7RoundedApply higham8_14_fanIn7RoundedMatrix
        rw [h76, h54]
        ext i
        symm
        calc
          matMulVec n
              (matMul n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
                (matMul n (fun i j => matMul n M3 M2 i j + Δ32 i j)
                  (fun i j => M1 i j + Δ1 i j))) b i =
              matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
                (matMulVec n
                  (matMul n (fun i j => matMul n M3 M2 i j + Δ32 i j)
                    (fun i j => M1 i j + Δ1 i j)) b) i :=
            matMulVec_matMul n
              (fun i j => matMul n C76 C54 i j + Δ7654 i j)
              (matMul n (fun i j => matMul n M3 M2 i j + Δ32 i j)
                (fun i j => M1 i j + Δ1 i j)) b i
          _ = matMulVec n (fun i j => matMul n C76 C54 i j + Δ7654 i j)
                (matMulVec n (fun i j => matMul n M3 M2 i j + Δ32 i j)
                  (matMulVec n (fun i j => M1 i j + Δ1 i j) b)) i := by
            congr 1
            funext j
            exact matMulVec_matMul n
              (fun i j => matMul n M3 M2 i j + Δ32 i j)
              (fun i j => M1 i j + Δ1 i j) b j
  · intro i j
    calc
      |Δ32 i j| = |(C32 i j - matMul n M3 M2 i j) + E32 i j| := by rfl
      _ ≤ |C32 i j - matMul n M3 M2 i j| + |E32 i j| := abs_add_le _ _
      _ ≤ gamma fp n * (∑ k : Fin n, |M3 i k| * |M2 k j|) +
          gamma fp n * |C32 i j| := by
        exact add_le_add
          (by simpa [C32, matMul] using matMul_error_bound fp n n n M3 M2 hn i j)
          (hE32 i j)
      _ = gamma fp n * (∑ k : Fin n, |M3 i k| * |M2 k j|) +
          gamma fp n * |fl_matMul fp n n n M3 M2 i j| := by rfl
  · intro i j
    simpa [Δ54, C54, matMul] using matMul_error_bound fp n n n M5 M4 hn i j
  · intro i j
    simpa [Δ76, C76, matMul] using matMul_error_bound fp n n n M7 M6 hn i j
  · intro i j
    calc
      |Δ7654 i j| = |(C7654 i j - matMul n C76 C54 i j) + E7654 i j| := by rfl
      _ ≤ |C7654 i j - matMul n C76 C54 i j| + |E7654 i j| := abs_add_le _ _
      _ ≤ gamma fp n * (∑ k : Fin n, |C76 i k| * |C54 k j|) +
          gamma fp n * |C7654 i j| := by
        exact add_le_add
          (by simpa [C7654, matMul] using matMul_error_bound fp n n n C76 C54 hn i j)
          (hE7654 i j)
      _ = gamma fp n *
              (∑ k : Fin n,
                |fl_matMul fp n n n M7 M6 i k| *
                  |fl_matMul fp n n n M5 M4 k j|) +
            gamma fp n *
              |fl_matMul fp n n n
                (fl_matMul fp n n n M7 M6)
                (fl_matMul fp n n n M5 M4) i j| := by rfl

/-! ### Exact all-orders envelope calculus for the literal fan-in tree -/

/-- An entrywise matrix envelope with scale `s`.  It records a nonnegative
majorant `E` for the exact matrix and an `(s-1)E` forward-error majorant for
its approximation.  This form composes through actual matrix products without
requiring a relative perturbation of a cancellation-prone intermediate. -/
def higham8_18MatrixEnvelope (n : ℕ)
    (Ahat A E : Fin n → Fin n → ℝ) (s : ℝ) : Prop :=
  (∀ i j, 0 ≤ E i j) ∧
    (∀ i j, |A i j| ≤ E i j) ∧
    (∀ i j, |Ahat i j - A i j| ≤ (s - 1) * E i j) ∧
    1 ≤ s

/-- Vector analogue of `higham8_18MatrixEnvelope`. -/
def higham8_18VectorEnvelope (n : ℕ)
    (xhat x E : Fin n → ℝ) (s : ℝ) : Prop :=
  (∀ i, 0 ≤ E i) ∧
    (∀ i, |x i| ≤ E i) ∧
    (∀ i, |xhat i - x i| ≤ (s - 1) * E i) ∧
    1 ≤ s

theorem higham8_18MatrixEnvelope_exact (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    higham8_18MatrixEnvelope n A A (absMatrix n A) 1 := by
  refine ⟨?_, ?_, ?_, le_rfl⟩
  · intro i j
    simp [absMatrix]
  · intro i j
    simp [absMatrix]
  · intro i j
    simp

theorem higham8_18VectorEnvelope_exact (n : ℕ) (x : Fin n → ℝ) :
    higham8_18VectorEnvelope n x x (absVec n x) 1 := by
  refine ⟨?_, ?_, ?_, le_rfl⟩
  · intro i
    simp [absVec]
  · intro i
    simp [absVec]
  · intro i
    simp

theorem higham8_18MatrixEnvelope_abs_approx_le {n : ℕ}
    {Ahat A E : Fin n → Fin n → ℝ} {s : ℝ}
    (h : higham8_18MatrixEnvelope n Ahat A E s) :
    ∀ i j, |Ahat i j| ≤ s * E i j := by
  intro i j
  calc
    |Ahat i j| = |(Ahat i j - A i j) + A i j| := by ring_nf
    _ ≤ |Ahat i j - A i j| + |A i j| := abs_add_le _ _
    _ ≤ (s - 1) * E i j + E i j :=
      add_le_add (h.2.2.1 i j) (h.2.1 i j)
    _ = s * E i j := by ring

theorem higham8_18VectorEnvelope_abs_approx_le {n : ℕ}
    {xhat x E : Fin n → ℝ} {s : ℝ}
    (h : higham8_18VectorEnvelope n xhat x E s) :
    ∀ i, |xhat i| ≤ s * E i := by
  intro i
  calc
    |xhat i| = |(xhat i - x i) + x i| := by ring_nf
    _ ≤ |xhat i - x i| + |x i| := abs_add_le _ _
    _ ≤ (s - 1) * E i + E i := add_le_add (h.2.2.1 i) (h.2.1 i)
    _ = s * E i := by ring

/-- Matrix envelopes compose through a literal rounded matrix product. -/
theorem higham8_18MatrixEnvelope_fl_matMul (fp : FPModel) (n : ℕ)
    (Ahat A EA Bhat B EB : Fin n → Fin n → ℝ) (sA sB : ℝ)
    (hn : gammaValid fp n)
    (hA : higham8_18MatrixEnvelope n Ahat A EA sA)
    (hB : higham8_18MatrixEnvelope n Bhat B EB sB) :
    higham8_18MatrixEnvelope n
      (fl_matMul fp n n n Ahat Bhat)
      (matMul n A B)
      (matMul n EA EB)
      ((1 + gamma fp n) * sA * sB) := by
  let g := gamma fp n
  have hg : 0 ≤ g := gamma_nonneg fp hn
  have hsA : 0 ≤ sA := le_trans zero_le_one hA.2.2.2
  have hsB : 0 ≤ sB := le_trans zero_le_one hB.2.2.2
  have hAhat := higham8_18MatrixEnvelope_abs_approx_le hA
  have hBhat := higham8_18MatrixEnvelope_abs_approx_le hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j))
  · intro i j
    unfold matMul
    calc
      |∑ k : Fin n, A i k * B k j| ≤
          ∑ k : Fin n, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |A i k| * |B k j| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
      _ ≤ ∑ k : Fin n, EA i k * EB k j := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (hA.2.1 i k) (hB.2.1 k j)
          (abs_nonneg _) (hA.1 i k)
  · intro i j
    let Phat := matMul n Ahat Bhat
    let P := matMul n A B
    have hlocal :
        |fl_matMul fp n n n Ahat Bhat i j - Phat i j| ≤
          g * (sA * sB) * matMul n EA EB i j := by
      have hraw := matMul_error_bound fp n n n Ahat Bhat hn i j
      calc
        |fl_matMul fp n n n Ahat Bhat i j - Phat i j| ≤
            g * ∑ k : Fin n, |Ahat i k| * |Bhat k j| := by
              simpa [Phat, matMul, g] using hraw
        _ ≤ g * ∑ k : Fin n, (sA * EA i k) * (sB * EB k j) := by
              apply mul_le_mul_of_nonneg_left _ hg
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul (hAhat i k) (hBhat k j)
                (abs_nonneg _) (mul_nonneg hsA (hA.1 i k))
        _ = g * (sA * sB) * matMul n EA EB i j := by
              unfold matMul
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    have hprop :
        |Phat i j - P i j| ≤
          (sA * sB - 1) * matMul n EA EB i j := by
      unfold Phat P matMul
      calc
        |(∑ k : Fin n, Ahat i k * Bhat k j) -
            ∑ k : Fin n, A i k * B k j| =
            |∑ k : Fin n,
              ((Ahat i k - A i k) * Bhat k j +
                A i k * (Bhat k j - B k j))| := by
                  congr 1
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro k _
                  ring
        _ ≤ ∑ k : Fin n,
            |(Ahat i k - A i k) * Bhat k j +
              A i k * (Bhat k j - B k j)| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin n,
            (((sA - 1) * EA i k) * (sB * EB k j) +
              EA i k * ((sB - 1) * EB k j)) := by
                apply Finset.sum_le_sum
                intro k _
                calc
                  |(Ahat i k - A i k) * Bhat k j +
                      A i k * (Bhat k j - B k j)| ≤
                      |Ahat i k - A i k| * |Bhat k j| +
                        |A i k| * |Bhat k j - B k j| := by
                          rw [← abs_mul, ← abs_mul]
                          exact abs_add_le _ _
                  _ ≤ ((sA - 1) * EA i k) * (sB * EB k j) +
                        EA i k * ((sB - 1) * EB k j) := by
                          exact add_le_add
                            (mul_le_mul (hA.2.2.1 i k) (hBhat k j)
                              (abs_nonneg _)
                              (mul_nonneg (sub_nonneg.mpr hA.2.2.2) (hA.1 i k)))
                            (mul_le_mul (hA.2.1 i k) (hB.2.2.1 k j)
                              (abs_nonneg _) (hA.1 i k))
        _ = (sA * sB - 1) * ∑ k : Fin n, EA i k * EB k j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    calc
      |fl_matMul fp n n n Ahat Bhat i j - matMul n A B i j| =
          |(fl_matMul fp n n n Ahat Bhat i j - Phat i j) +
            (Phat i j - P i j)| := by
              dsimp [P]
              congr 1
              ring
      _ ≤ |fl_matMul fp n n n Ahat Bhat i j - Phat i j| +
          |Phat i j - P i j| := abs_add_le _ _
      _ ≤ g * (sA * sB) * matMul n EA EB i j +
          (sA * sB - 1) * matMul n EA EB i j := add_le_add hlocal hprop
      _ = ((1 + gamma fp n) * sA * sB - 1) * matMul n EA EB i j := by
          dsimp [g]
          ring
  · have hone : 1 ≤ 1 + gamma fp n := by linarith
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1 * 1)
      (mul_le_mul (mul_le_mul hone hA.2.2.2 zero_le_one (by linarith))
        hB.2.2.2 zero_le_one (mul_nonneg (by linarith) hsA))

/-- Matrix and vector envelopes compose through a literal rounded
matrix-vector product. -/
theorem higham8_18VectorEnvelope_fl_matVec (fp : FPModel) (n : ℕ)
    (Ahat A EA : Fin n → Fin n → ℝ)
    (xhat x Ex : Fin n → ℝ) (sA sx : ℝ)
    (hn : gammaValid fp n)
    (hA : higham8_18MatrixEnvelope n Ahat A EA sA)
    (hx : higham8_18VectorEnvelope n xhat x Ex sx) :
    higham8_18VectorEnvelope n
      (fl_matVec fp n n Ahat xhat)
      (matMulVec n A x)
      (matMulVec n EA Ex)
      ((1 + gamma fp n) * sA * sx) := by
  let g := gamma fp n
  have hg : 0 ≤ g := gamma_nonneg fp hn
  have hsA : 0 ≤ sA := le_trans zero_le_one hA.2.2.2
  have hsx : 0 ≤ sx := le_trans zero_le_one hx.2.2.2
  have hAhat := higham8_18MatrixEnvelope_abs_approx_le hA
  have hxhat := higham8_18VectorEnvelope_abs_approx_le hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA.1 i k) (hx.1 k))
  · intro i
    unfold matMulVec
    calc
      |∑ k : Fin n, A i k * x k| ≤
          ∑ k : Fin n, |A i k * x k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |A i k| * |x k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
      _ ≤ ∑ k : Fin n, EA i k * Ex k := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (hA.2.1 i k) (hx.2.1 k) (abs_nonneg _) (hA.1 i k)
  · intro i
    let phat := matMulVec n Ahat xhat
    let p := matMulVec n A x
    have hlocal :
        |fl_matVec fp n n Ahat xhat i - phat i| ≤
          g * (sA * sx) * matMulVec n EA Ex i := by
      have hraw := matVec_error_bound fp n n Ahat xhat hn i
      calc
        |fl_matVec fp n n Ahat xhat i - phat i| ≤
            g * ∑ k : Fin n, |Ahat i k| * |xhat k| := by
              simpa [phat, matMulVec, g] using hraw
        _ ≤ g * ∑ k : Fin n, (sA * EA i k) * (sx * Ex k) := by
              apply mul_le_mul_of_nonneg_left _ hg
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul (hAhat i k) (hxhat k)
                (abs_nonneg _) (mul_nonneg hsA (hA.1 i k))
        _ = g * (sA * sx) * matMulVec n EA Ex i := by
              unfold matMulVec
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    have hprop :
        |phat i - p i| ≤
          (sA * sx - 1) * matMulVec n EA Ex i := by
      unfold phat p matMulVec
      calc
        |(∑ k : Fin n, Ahat i k * xhat k) - ∑ k : Fin n, A i k * x k| =
            |∑ k : Fin n,
              ((Ahat i k - A i k) * xhat k + A i k * (xhat k - x k))| := by
                congr 1
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ ≤ ∑ k : Fin n,
            |(Ahat i k - A i k) * xhat k + A i k * (xhat k - x k)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin n,
            (((sA - 1) * EA i k) * (sx * Ex k) +
              EA i k * ((sx - 1) * Ex k)) := by
                apply Finset.sum_le_sum
                intro k _
                calc
                  |(Ahat i k - A i k) * xhat k + A i k * (xhat k - x k)| ≤
                      |Ahat i k - A i k| * |xhat k| +
                        |A i k| * |xhat k - x k| := by
                          rw [← abs_mul, ← abs_mul]
                          exact abs_add_le _ _
                  _ ≤ ((sA - 1) * EA i k) * (sx * Ex k) +
                        EA i k * ((sx - 1) * Ex k) := by
                          exact add_le_add
                            (mul_le_mul (hA.2.2.1 i k) (hxhat k)
                              (abs_nonneg _)
                              (mul_nonneg (sub_nonneg.mpr hA.2.2.2) (hA.1 i k)))
                            (mul_le_mul (hA.2.1 i k) (hx.2.2.1 k)
                              (abs_nonneg _) (hA.1 i k))
        _ = (sA * sx - 1) * ∑ k : Fin n, EA i k * Ex k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    calc
      |fl_matVec fp n n Ahat xhat i - matMulVec n A x i| =
          |(fl_matVec fp n n Ahat xhat i - phat i) + (phat i - p i)| := by
            dsimp [p]
            congr 1
            ring
      _ ≤ |fl_matVec fp n n Ahat xhat i - phat i| + |phat i - p i| :=
        abs_add_le _ _
      _ ≤ g * (sA * sx) * matMulVec n EA Ex i +
          (sA * sx - 1) * matMulVec n EA Ex i := add_le_add hlocal hprop
      _ = ((1 + gamma fp n) * sA * sx - 1) * matMulVec n EA Ex i := by
        dsimp [g]
        ring
  · have hone : 1 ≤ 1 + gamma fp n := by linarith
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1 * 1)
      (mul_le_mul (mul_le_mul hone hA.2.2.2 zero_le_one (by linarith))
        hx.2.2.2 zero_le_one (mul_nonneg (by linarith) hsA))

/-- Product-of-absolute-matrices majorant in the parenthesization of the
source's seven-factor fan-in tree. -/
noncomputable def higham8_18_fanIn7AbsMatrix (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n
    (matMul n
      (matMul n (absMatrix n M7) (absMatrix n M6))
      (matMul n (absMatrix n M5) (absMatrix n M4)))
    (matMul n
      (matMul n (absMatrix n M3) (absMatrix n M2))
      (absMatrix n M1))

/-- For the genuine inverse column factors, the `(8.18)` product of absolute
matrices is exactly the inverse of the comparison matrix `M(L)`.  This is the
source identity `|M₇|⋯|M₁| = M(L)⁻¹`, now derived from the literal
`M_k=L_k⁻¹` producers. -/
theorem higham8_18_fanIn7AbsMatrix_eq_comparisonInverse
    (L C_inv : Fin 7 → Fin 7 → ℝ)
    (hLT : ∀ i j : Fin 7, i.val < j.val → L i j = 0)
    (hdiag : ∀ k : Fin 7, L k k ≠ 0)
    (hCright : IsRightInverse 7 (comparisonMatrix 7 L) C_inv) :
    higham8_18_fanIn7AbsMatrix 7
        (higham8_13_lowerColumnInverseFactor 7 L 0)
        (higham8_13_lowerColumnInverseFactor 7 L 1)
        (higham8_13_lowerColumnInverseFactor 7 L 2)
        (higham8_13_lowerColumnInverseFactor 7 L 3)
        (higham8_13_lowerColumnInverseFactor 7 L 4)
        (higham8_13_lowerColumnInverseFactor 7 L 5)
        (higham8_13_lowerColumnInverseFactor 7 L 6) = C_inv := by
  have hCLT : ∀ i j : Fin 7, i.val < j.val →
      comparisonMatrix 7 L i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by omega
    simp [comparisonMatrix, hne, hLT i j hij]
  have hCdiag : ∀ k : Fin 7, comparisonMatrix 7 L k k ≠ 0 := by
    intro k
    simp [comparisonMatrix, hdiag k]
  have hCleft : IsLeftInverse 7 (comparisonMatrix 7 L)
      (higham8_13_inverseColumnProduct 7 (comparisonMatrix 7 L)) :=
    (higham8_13_inverseColumnProduct_inverse 7 (comparisonMatrix 7 L)
      hCLT hCdiag).1
  change higham8_13_fanIn7Matrix 7
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 0))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 1))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 2))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 3))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 4))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 5))
      (absMatrix 7 (higham8_13_lowerColumnInverseFactor 7 L 6)) = C_inv
  rw [higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor,
    higham8_13_abs_lowerColumnInverseFactor]
  rw [higham8_13_fanIn7InverseMatrix_eq]
  exact higham8_13_leftInverse_eq_rightInverse
    (comparisonMatrix 7 L)
    (higham8_13_inverseColumnProduct 7 (comparisonMatrix 7 L)) C_inv
    hCleft hCright

/-- The `(8.18)` source majorant `|M7|⋯|M1||b|`, with the same harmless
fan-in parenthesization as the literal executor. -/
noncomputable def higham8_18_fanIn7AbsApply (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) : Fin n → ℝ :=
  matMulVec n (higham8_18_fanIn7AbsMatrix n M1 M2 M3 M4 M5 M6 M7)
    (absVec n b)

/-- Exact quadratic-and-higher coefficient hidden by the `O(u²)` in the
seven-operation fan-in bound.  Writing `a = n*u` and `g = gamma_n`, this is
`7*a²/(1-a)` (the higher-order part of `7*g`) plus the degree-two-through-seven
terms of `(1+g)^7`. -/
noncomputable def higham8_18_fanIn7CoefficientRemainder
    (fp : FPModel) (n : ℕ) : ℝ :=
  let a := (n : ℝ) * fp.u
  let g := gamma fp n
  7 * (a ^ 2 / (1 - a)) +
    21 * g ^ 2 + 35 * g ^ 3 + 35 * g ^ 4 +
      21 * g ^ 5 + 7 * g ^ 6 + g ^ 7

theorem higham8_18_fanIn7Coefficient_eq_first_order_add_remainder
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    (1 + gamma fp n) ^ 7 - 1 =
      7 * (n : ℝ) * fp.u +
        higham8_18_fanIn7CoefficientRemainder fp n := by
  have hg := gamma_eq_linear_plus_quadratic_remainder fp n hn
  unfold higham8_18_fanIn7CoefficientRemainder
  dsimp only
  rw [hg]
  ring

theorem higham8_18_fanIn7CoefficientRemainder_nonneg
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ higham8_18_fanIn7CoefficientRemainder fp n := by
  have hden : 0 < 1 - (n : ℝ) * fp.u := by
    unfold gammaValid at hn
    linarith
  have hg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  unfold higham8_18_fanIn7CoefficientRemainder
  dsimp only
  positivity

/-- **Equation (8.18), literal-executor all-orders form.**  The actual seven
rounded operations satisfy the source's product-of-absolute-matrices forward
envelope.  The exact coefficient `(1+γₙ)^7-1` retains all higher-order terms;
its first-order term is `7γₙ`, matching the source's `d'ₙ u + O(u²)` form.

No relative perturbation of an intermediate product is assumed, so exact
cancellation in `M3*M2`, `M5*M4`, or `M7*M6` is allowed. -/
theorem higham8_18_fanIn7Executor_forward_componentwise_bound
    (fp : FPModel) (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n) :
    ∀ i : Fin n,
      |higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i -
        higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i| ≤
      ((1 + gamma fp n) ^ 7 - 1) *
        higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i := by
  let q : ℝ := 1 + gamma fp n
  let P76 := matMul n M7 M6
  let P54 := matMul n M5 M4
  let P7654 := matMul n P76 P54
  let P32 := matMul n M3 M2
  let x1 := matMulVec n M1 b
  let x321 := matMulVec n P32 x1
  let x := matMulVec n P7654 x321
  let E76 := matMul n (absMatrix n M7) (absMatrix n M6)
  let E54 := matMul n (absMatrix n M5) (absMatrix n M4)
  let E7654 := matMul n E76 E54
  let E32 := matMul n (absMatrix n M3) (absMatrix n M2)
  let e1 := matMulVec n (absMatrix n M1) (absVec n b)
  let e321 := matMulVec n E32 e1
  let e := matMulVec n E7654 e321
  let C76 := fl_matMul fp n n n M7 M6
  let C54 := fl_matMul fp n n n M5 M4
  let C7654 := fl_matMul fp n n n C76 C54
  let C32 := fl_matMul fp n n n M3 M2
  let v1 := fl_matVec fp n n M1 b
  let v321 := fl_matVec fp n n C32 v1
  let xhat := fl_matVec fp n n C7654 v321
  have hM1 := higham8_18MatrixEnvelope_exact n M1
  have hM2 := higham8_18MatrixEnvelope_exact n M2
  have hM3 := higham8_18MatrixEnvelope_exact n M3
  have hM4 := higham8_18MatrixEnvelope_exact n M4
  have hM5 := higham8_18MatrixEnvelope_exact n M5
  have hM6 := higham8_18MatrixEnvelope_exact n M6
  have hM7 := higham8_18MatrixEnvelope_exact n M7
  have hb := higham8_18VectorEnvelope_exact n b
  have h76 : higham8_18MatrixEnvelope n C76 P76 E76 q := by
    simpa [C76, P76, E76, q] using
      higham8_18MatrixEnvelope_fl_matMul fp n M7 M7 (absMatrix n M7)
        M6 M6 (absMatrix n M6) 1 1 hn hM7 hM6
  have h54 : higham8_18MatrixEnvelope n C54 P54 E54 q := by
    simpa [C54, P54, E54, q] using
      higham8_18MatrixEnvelope_fl_matMul fp n M5 M5 (absMatrix n M5)
        M4 M4 (absMatrix n M4) 1 1 hn hM5 hM4
  have h7654 :
      higham8_18MatrixEnvelope n C7654 P7654 E7654 (q * q * q) := by
    simpa [C7654, P7654, E7654, q] using
      higham8_18MatrixEnvelope_fl_matMul fp n C76 P76 E76 C54 P54 E54
        q q hn h76 h54
  have h32 : higham8_18MatrixEnvelope n C32 P32 E32 q := by
    simpa [C32, P32, E32, q] using
      higham8_18MatrixEnvelope_fl_matMul fp n M3 M3 (absMatrix n M3)
        M2 M2 (absMatrix n M2) 1 1 hn hM3 hM2
  have hv1 : higham8_18VectorEnvelope n v1 x1 e1 q := by
    simpa [v1, x1, e1, q] using
      higham8_18VectorEnvelope_fl_matVec fp n M1 M1 (absMatrix n M1)
        b b (absVec n b) 1 1 hn hM1 hb
  have hv321 :
      higham8_18VectorEnvelope n v321 x321 e321 (q * q * q) := by
    simpa [v321, x321, e321, q] using
      higham8_18VectorEnvelope_fl_matVec fp n C32 P32 E32 v1 x1 e1
        q q hn h32 hv1
  have hxhat0 :
      higham8_18VectorEnvelope n xhat x e
        (q * (q * q * q) * (q * q * q)) := by
    simpa [xhat, x, e, q] using
      higham8_18VectorEnvelope_fl_matVec fp n C7654 P7654 E7654
        v321 x321 e321 (q * q * q) (q * q * q) hn h7654 hv321
  have hscale : q * (q * q * q) * (q * q * q) = q ^ 7 := by ring
  have hxhat : higham8_18VectorEnvelope n xhat x e (q ^ 7) := by
    simpa [hscale] using hxhat0
  have hmv (A B : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
      matMulVec n (matMul n A B) v = matMulVec n A (matMulVec n B v) := by
    funext i
    exact matMulVec_matMul n A B v i
  have hx : x = higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b := by
    ext i
    simp [x, x321, x1, P7654, P76, P54, P32,
      higham8_13_fanIn7Apply, higham8_13_fanIn7Matrix, hmv]
  have he : e = higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b := by
    ext i
    simp [e, e321, e1, E7654, E76, E54, E32,
      higham8_18_fanIn7AbsApply, higham8_18_fanIn7AbsMatrix,
      hmv]
  intro i
  have herr := hxhat.2.2.1 i
  simpa [xhat, higham8_14_fanIn7Executor, hx, he, q] using herr

/-- **Equation (8.18), literal first-order-plus-remainder form.**  The actual
fan-in executor coefficient is split into the source's `7*n*u` first-order
term and a named, nonnegative exact remainder.  No relative error of a
cancellation-prone intermediate product is assumed. -/
theorem higham8_18_fanIn7Executor_forward_first_order_remainder_bound
    (fp : FPModel) (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n) :
    ∀ i : Fin n,
      |higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i -
        higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i| ≤
      (7 * (n : ℝ) * fp.u) *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i +
        higham8_18_fanIn7CoefficientRemainder fp n *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i := by
  intro i
  have h := higham8_18_fanIn7Executor_forward_componentwise_bound
    fp n M1 M2 M3 M4 M5 M6 M7 b hn i
  rw [higham8_18_fanIn7Coefficient_eq_first_order_add_remainder fp n hn] at h
  nlinarith

/-- **Equation (8.19), literal-executor relative `∞`-norm form.** -/
theorem higham8_19_fanIn7Executor_forward_relative_infNorm_bound
    (fp : FPModel) (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hx : 0 < infNormVec
      (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)) :
    infNormVec
        (fun i =>
          higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i -
            higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i) /
        infNormVec (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) ≤
      infNormVec
        (fun i =>
          ((1 + gamma fp n) ^ 7 - 1) *
            higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i) /
        infNormVec (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) := by
  have hnorm :
      infNormVec
          (fun i =>
            higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i -
              higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i) ≤
        infNormVec
          (fun i =>
            ((1 + gamma fp n) ^ 7 - 1) *
              higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i) := by
    apply infNormVec_le_of_abs_le
    · intro i
      exact le_trans
        (higham8_18_fanIn7Executor_forward_componentwise_bound
          fp n M1 M2 M3 M4 M5 M6 M7 b hn i)
        (le_trans (le_abs_self _)
          (abs_le_infNormVec
            (fun j =>
              ((1 + gamma fp n) ^ 7 - 1) *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j)
            i))
    · exact infNormVec_nonneg _
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hx)

/-- **Equation (8.18), finite-product form**: a componentwise perturbation
bound for the fan-in product gives a componentwise forward-error bound after
applying the product to `b`. -/
theorem higham8_18_fanIn_forward_componentwise_bound (n m : ℕ)
    (M ΔM : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (b : Fin n → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔM r i j| ≤ δ r * |M r i j|) :
    ∀ i : Fin n,
      |matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b i -
        matMulVec n (matSeqProd n m M) b i| ≤
        matMulVec n
          (fun i j =>
            (scalarSeqProd m (fun r => 1 + δ r) - 1) *
              matSeqProd n m (fun r => absMatrix n (M r)) i j)
          (absVec n b) i := by
  intro i
  have hprod :=
    matSeqProd_componentwise_perturbation_bound n m M ΔM δ hδ hΔ
  unfold matMulVec
  calc
    |(∑ j : Fin n,
        matSeqProd n m (fun r i j => M r i j + ΔM r i j) i j * b j) -
        ∑ j : Fin n, matSeqProd n m M i j * b j|
        =
          |∑ j : Fin n,
            (matSeqProd n m (fun r i j => M r i j + ΔM r i j) i j -
              matSeqProd n m M i j) * b j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ ≤
        ∑ j : Fin n,
          |(matSeqProd n m (fun r i j => M r i j + ΔM r i j) i j -
            matSeqProd n m M i j) * b j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ =
        ∑ j : Fin n,
          |matSeqProd n m (fun r i j => M r i j + ΔM r i j) i j -
            matSeqProd n m M i j| * |b j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul
            (matSeqProd n m (fun r i j => M r i j + ΔM r i j) i j -
              matSeqProd n m M i j) (b j)
    _ ≤
        ∑ j : Fin n,
          ((scalarSeqProd m (fun r => 1 + δ r) - 1) *
            matSeqProd n m (fun r => absMatrix n (M r)) i j) * |b j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hprod i j) (abs_nonneg (b j))
    _ =
        ∑ j : Fin n,
          ((scalarSeqProd m (fun r => 1 + δ r) - 1) *
            matSeqProd n m (fun r => absMatrix n (M r)) i j) *
              absVec n b j := by
          simp [absVec]

/-- **Equation (8.19)**: relative `∞`-norm forward-error form of the finite
fan-in product perturbation bound. -/
theorem higham8_19_fanIn_forward_relative_infNorm_bound (n m : ℕ)
    (M ΔM : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (b : Fin n → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔM r i j| ≤ δ r * |M r i j|)
    (hx : 0 < infNormVec (matMulVec n (matSeqProd n m M) b)) :
    infNormVec
      (fun i =>
        matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b i -
          matMulVec n (matSeqProd n m M) b i) /
        infNormVec (matMulVec n (matSeqProd n m M) b) ≤
      infNormVec
        (matMulVec n
          (fun i j =>
            (scalarSeqProd m (fun r => 1 + δ r) - 1) *
              matSeqProd n m (fun r => absMatrix n (M r)) i j)
          (absVec n b)) /
        infNormVec (matMulVec n (matSeqProd n m M) b) := by
  have hnorm :
      infNormVec
        (fun i =>
          matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b i -
            matMulVec n (matSeqProd n m M) b i) ≤
        infNormVec
          (matMulVec n
            (fun i j =>
              (scalarSeqProd m (fun r => 1 + δ r) - 1) *
                matSeqProd n m (fun r => absMatrix n (M r)) i j)
            (absVec n b)) := by
    apply infNormVec_le_of_abs_le
    · intro i
      exact le_trans
        (higham8_18_fanIn_forward_componentwise_bound n m M ΔM δ b hδ hΔ i)
        (le_trans (le_abs_self _) (abs_le_infNormVec _ i))
    · exact infNormVec_nonneg _
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hx)

/-! ### Why the local `(8.14)` envelopes cannot be made relative to a
cancelled intermediate product

The source bounds the local product errors by sums containing `|A||B|` and
`|AB|`.  The finite-product bridge above instead asks for a scalar relative
bound by `|AB|` alone.  The following literal two-by-two witness records the
sharp obstruction: `AB` cancels to zero while `|A||B|` is nonzero. -/

private def higham8_14_cancellationLeft : Fin 2 → Fin 2 → ℝ :=
  fun i _ => if i = 0 then 1 else 0

private def higham8_14_cancellationRight : Fin 2 → Fin 2 → ℝ :=
  fun k j => if j = 0 then (if k = 0 then 1 else -1) else 0

private def higham8_14_cancellationDelta : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- **Sharp bridge blocker for (8.14)--(8.15).**  A perturbation can obey the
actual local product-of-absolute-matrices envelope while no finite scalar
relative perturbation bound by the cancelled exact intermediate product is
possible.  Thus `higham8_15_fanIn_residual_componentwise_bound` cannot be
instantiated from the local `(8.14)` hypotheses without an additional
first-order expansion (whose cross terms belong to the source's `O(u²)`). -/
theorem higham8_14_local_envelope_not_relative_after_cancellation :
    matMul 2 higham8_14_cancellationLeft higham8_14_cancellationRight 0 0 = 0 ∧
    matMul 2
        (absMatrix 2 higham8_14_cancellationLeft)
        (absMatrix 2 higham8_14_cancellationRight) 0 0 = 2 ∧
    |higham8_14_cancellationDelta 0 0| ≤
        (1 / 2 : ℝ) *
          (matMul 2
              (absMatrix 2 higham8_14_cancellationLeft)
              (absMatrix 2 higham8_14_cancellationRight) 0 0 +
            |matMul 2 higham8_14_cancellationLeft
              higham8_14_cancellationRight 0 0|) ∧
    ∀ δ : ℝ,
      ¬ |higham8_14_cancellationDelta 0 0| ≤
        δ * |matMul 2 higham8_14_cancellationLeft
          higham8_14_cancellationRight 0 0| := by
  constructor
  · norm_num [matMul, higham8_14_cancellationLeft,
      higham8_14_cancellationRight, Fin.sum_univ_two]
  constructor
  · norm_num [matMul, absMatrix, higham8_14_cancellationLeft,
      higham8_14_cancellationRight, Fin.sum_univ_two]
  constructor
  · norm_num [matMul, absMatrix, higham8_14_cancellationLeft,
      higham8_14_cancellationRight, higham8_14_cancellationDelta,
      Fin.sum_univ_two]
  · intro δ h
    norm_num [matMul, higham8_14_cancellationLeft,
      higham8_14_cancellationRight, higham8_14_cancellationDelta,
      Fin.sum_univ_two] at h

/-- **Equation (8.15), residual transfer**: any componentwise forward-error
envelope `E` gives a componentwise residual envelope after multiplying by
`|L|`. -/
theorem higham8_15_residual_componentwise_of_forward_error (n : ℕ)
    (L : Fin n → Fin n → ℝ) (x xhat b E : Fin n → ℝ)
    (hsolve : matMulVec n L x = b)
    (hE : ∀ i : Fin n, |xhat i - x i| ≤ E i) :
    ∀ i : Fin n,
      |b i - matMulVec n L xhat i| ≤
        matMulVec n (absMatrix n L) E i := by
  intro i
  have hb : b i = matMulVec n L x i := by
    exact (congrFun hsolve i).symm
  calc
    |b i - matMulVec n L xhat i|
        = |matMulVec n L x i - matMulVec n L xhat i| := by rw [hb]
    _ =
        |matMulVec n L (fun j => x j - xhat j) i| := by
          congr 1
          unfold matMulVec
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ ≤ ∑ j : Fin n, |L i j| * |x j - xhat j| :=
        abs_matMulVec_le n L (fun j => x j - xhat j) i
    _ ≤ ∑ j : Fin n, |L i j| * E j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (by simpa [abs_sub_comm] using hE j) (abs_nonneg (L i j))
    _ = matMulVec n (absMatrix n L) E i := by
        simp [matMulVec, absMatrix]

/-- **Equation (8.15), literal-executor all-orders residual form.**  Composing
the actual `(8.14)` executor with the exact `(8.18)` envelope gives the raw
residual majorant `|L| (((1+γₙ)^7-1)|M₇|⋯|M₁||b|)`.  Rewriting its
first-order part directly as the five-factor source cube is not valid in
general; `HighamChapter8FanInClosure` gives an exact order-seven counterexample.
The source obtains its displayed asymptotic cube from a local perturbation
expansion before placing cross terms in `O(u²)`. -/
theorem higham8_15_fanIn7Executor_residual_componentwise_bound
    (fp : FPModel) (n : ℕ)
    (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b) :
    ∀ i : Fin n,
      |b i - matMulVec n L
        (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) i| ≤
        matMulVec n (absMatrix n L)
          (fun j =>
            ((1 + gamma fp n) ^ 7 - 1) *
              higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j) i := by
  exact higham8_15_residual_componentwise_of_forward_error n L
    (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)
    (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) b
    (fun j =>
      ((1 + gamma fp n) ^ 7 - 1) *
        higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j)
    hsolve
    (higham8_18_fanIn7Executor_forward_componentwise_bound
      fp n M1 M2 M3 M4 M5 M6 M7 b hn)

/-- **Equation (8.15), literal raw-envelope first-order split.**  This closes
the scalar expansion for the exact all-orders substitute: the first-order raw
residual is `7*n*u` times `|L| |M7|⋯|M1| |b|`, and the rest is the named
exact nonnegative coefficient remainder applied to the same majorant.  This
global raw split is not Higham's local first-order expansion and is not claimed
to reduce pointwise to the printed five-factor cube. -/
theorem higham8_15_fanIn7Executor_residual_first_order_remainder_bound
    (fp : FPModel) (n : ℕ)
    (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b) :
    ∀ i : Fin n,
      |b i - matMulVec n L
        (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) i| ≤
        matMulVec n (absMatrix n L)
          (fun j =>
            (7 * (n : ℝ) * fp.u) *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j +
              higham8_18_fanIn7CoefficientRemainder fp n *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j) i := by
  exact higham8_15_residual_componentwise_of_forward_error n L
    (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)
    (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) b
    (fun j =>
      (7 * (n : ℝ) * fp.u) *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j +
        higham8_18_fanIn7CoefficientRemainder fp n *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j)
    hsolve
    (higham8_18_fanIn7Executor_forward_first_order_remainder_bound
      fp n M1 M2 M3 M4 M5 M6 M7 b hn)

/-- **Equation (8.16), literal-executor all-orders norm form.** -/
theorem higham8_16_fanIn7Executor_residual_infNorm_bound
    (fp : FPModel) (n : ℕ)
    (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b) :
    infNormVec
        (fun i => b i - matMulVec n L
          (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) i) ≤
      infNormVec
        (matMulVec n (absMatrix n L)
          (fun j =>
            ((1 + gamma fp n) ^ 7 - 1) *
              higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j)) := by
  apply infNormVec_le_of_abs_le
  · intro i
    exact le_trans
      (higham8_15_fanIn7Executor_residual_componentwise_bound
        fp n L M1 M2 M3 M4 M5 M6 M7 b hn hsolve i)
      (le_trans (le_abs_self _)
        (abs_le_infNormVec
          (matMulVec n (absMatrix n L)
            (fun j =>
              ((1 + gamma fp n) ^ 7 - 1) *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b j)) i))
  · exact infNormVec_nonneg _

/-- **Equations (8.15)--(8.16), fan-in residual bound**: applying the
finite-product forward envelope from (8.18) to `L x = b` yields the
componentwise residual bound used before taking norms. -/
theorem higham8_15_fanIn_residual_componentwise_bound (n m : ℕ)
    (L : Fin n → Fin n → ℝ)
    (M ΔM : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (b : Fin n → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔM r i j| ≤ δ r * |M r i j|)
    (hsolve :
      matMulVec n L (matMulVec n (matSeqProd n m M) b) = b) :
    ∀ i : Fin n,
      |b i -
        matMulVec n L
          (matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b) i| ≤
        matMulVec n (absMatrix n L)
          (matMulVec n
            (fun i j =>
              (scalarSeqProd m (fun r => 1 + δ r) - 1) *
                matSeqProd n m (fun r => absMatrix n (M r)) i j)
            (absVec n b)) i := by
  let x : Fin n → ℝ := matMulVec n (matSeqProd n m M) b
  let xhat : Fin n → ℝ :=
    matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b
  let E : Fin n → ℝ :=
    matMulVec n
      (fun i j =>
        (scalarSeqProd m (fun r => 1 + δ r) - 1) *
          matSeqProd n m (fun r => absMatrix n (M r)) i j)
      (absVec n b)
  have hE : ∀ i : Fin n, |xhat i - x i| ≤ E i := by
    intro i
    simpa [x, xhat, E, abs_sub_comm] using
      higham8_18_fanIn_forward_componentwise_bound n m M ΔM δ b hδ hΔ i
  simpa [x, xhat, E] using
    higham8_15_residual_componentwise_of_forward_error n L x xhat b E hsolve hE

/-- **Equation (8.16)**: the `∞`-norm form of the fan-in residual bound. -/
theorem higham8_16_fanIn_residual_infNorm_bound (n m : ℕ)
    (L : Fin n → Fin n → ℝ)
    (M ΔM : Fin m → Fin n → Fin n → ℝ) (δ : Fin m → ℝ)
    (b : Fin n → ℝ)
    (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, |ΔM r i j| ≤ δ r * |M r i j|)
    (hsolve :
      matMulVec n L (matMulVec n (matSeqProd n m M) b) = b) :
    infNormVec
      (fun i =>
        b i -
          matMulVec n L
            (matMulVec n (matSeqProd n m (fun r i j => M r i j + ΔM r i j)) b) i) ≤
      infNormVec
        (matMulVec n (absMatrix n L)
          (matMulVec n
            (fun i j =>
              (scalarSeqProd m (fun r => 1 + δ r) - 1) *
                matSeqProd n m (fun r => absMatrix n (M r)) i j)
            (absVec n b))) := by
  apply infNormVec_le_of_abs_le
  · intro i
    exact le_trans
      (higham8_15_fanIn_residual_componentwise_bound n m L M ΔM δ b hδ hΔ hsolve i)
      (le_trans (le_abs_self _)
        (abs_le_infNormVec _ i))
  · exact infNormVec_nonneg _

/-- **Equation (8.17) support**: rank-one backward perturbation built from a
residual vector and one nonzero component of the computed solution. -/
noncomputable def higham8_17_rankOneBackwardDelta {n : ℕ}
    (r xhat : Fin n → ℝ) (j0 : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if j = j0 then r i / xhat j0 else 0

/-- **Equation (8.17) support**: the rank-one correction maps `xhat` to the
specified residual. -/
theorem higham8_17_rankOneBackwardDelta_mulVec {n : ℕ}
    (r xhat : Fin n → ℝ) (j0 : Fin n) (hxj0 : xhat j0 ≠ 0) :
    matMulVec n (higham8_17_rankOneBackwardDelta r xhat j0) xhat = r := by
  ext i
  unfold matMulVec higham8_17_rankOneBackwardDelta
  simp [hxj0]

/-- **Equation (8.17) support**: infinity-norm size of the rank-one backward
correction. -/
theorem higham8_17_rankOneBackwardDelta_infNorm_le {n : ℕ}
    (r xhat : Fin n → ℝ) (j0 : Fin n) :
    infNorm (higham8_17_rankOneBackwardDelta r xhat j0) ≤
      infNormVec r / |xhat j0| := by
  apply infNorm_le_of_row_sum_le
  · intro i
    unfold higham8_17_rankOneBackwardDelta
    calc
      ∑ j : Fin n, |(if j = j0 then r i / xhat j0 else 0)|
          = |r i / xhat j0| := by
            rw [Finset.sum_eq_single j0]
            · simp
            · intro j _ hj
              simp [hj]
            · intro hj
              exact (hj (Finset.mem_univ j0)).elim
      _ = |r i| / |xhat j0| := by
            rw [abs_div]
      _ ≤ infNormVec r / |xhat j0| :=
            div_le_div_of_nonneg_right (abs_le_infNormVec r i) (abs_nonneg _)
  · exact div_nonneg (infNormVec_nonneg r) (abs_nonneg _)

/-- **Equation (8.17)**: a residual bound gives a normwise backward-error
perturbation `(L + ΔL) xhat = b`.  Choosing `j0` as a maximum component of
`xhat` turns the denominator into `‖xhat‖∞`, matching the source's
normwise-backward-error route. -/
theorem higham8_17_backward_error_from_residual_infNorm_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ) (xhat b : Fin n → ℝ)
    (j0 : Fin n) (hxj0 : xhat j0 ≠ 0) (ρ : ℝ)
    (hρ :
      infNormVec (fun i => b i - matMulVec n L xhat i) / |xhat j0| ≤ ρ) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      matMulVec n (fun i j => L i j + ΔL i j) xhat = b ∧
        infNorm ΔL ≤ ρ := by
  let r : Fin n → ℝ := fun i => b i - matMulVec n L xhat i
  let ΔL : Fin n → Fin n → ℝ := higham8_17_rankOneBackwardDelta r xhat j0
  refine ⟨ΔL, ?_, ?_⟩
  · ext i
    have hdelta :=
      congrFun (higham8_17_rankOneBackwardDelta_mulVec r xhat j0 hxj0) i
    calc
      matMulVec n (fun i j => L i j + ΔL i j) xhat i
          = matMulVec n L xhat i + matMulVec n ΔL xhat i := by
            exact congrFun (matMulVec_add_left n L ΔL xhat) i
      _ = matMulVec n L xhat i + r i := by
            rw [hdelta]
      _ = b i := by
            dsimp [r]
            ring_nf
  · exact le_trans (higham8_17_rankOneBackwardDelta_infNorm_le r xhat j0) hρ

/-- **Equation (8.17), literal-executor all-orders backward-error form.**  The
actual `(8.14)` executor and `(8.16)` residual norm bound construct a rank-one
backward perturbation with the corresponding explicit raw envelope. -/
theorem higham8_17_fanIn7Executor_backward_error_bound
    (fp : FPModel) (n : ℕ)
    (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b)
    (j0 : Fin n)
    (hxj0 :
      higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b j0 ≠ 0) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      matMulVec n (fun i j => L i j + ΔL i j)
          (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) = b ∧
        infNorm ΔL ≤
          infNormVec
              (matMulVec n (absMatrix n L)
                (fun k =>
                  ((1 + gamma fp n) ^ 7 - 1) *
                    higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b k)) /
            |higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b j0| := by
  apply higham8_17_backward_error_from_residual_infNorm_bound n L
    (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) b j0 hxj0
  exact div_le_div_of_nonneg_right
    (higham8_16_fanIn7Executor_residual_infNorm_bound
      fp n L M1 M2 M3 M4 M5 M6 M7 b hn hsolve)
    (abs_nonneg _)

/-- **Equation (8.20) support**: the source residual envelope before the final
left multiplication by `|L⁻¹|`, namely `|L||L⁻¹||L||L⁻¹||L|`. -/
noncomputable def higham8_15_residualCubeBase (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (absMatrix n L)
    (matMul n (absMatrix n L_inv)
      (matMul n (absMatrix n L)
        (matMul n (absMatrix n L_inv) (absMatrix n L))))

/-- **Equation (8.20) support**: the condition-cubing matrix
`(|L⁻¹||L|)^3`. -/
noncomputable def higham8_20_absCondCube (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (absMatrix n L_inv) (higham8_15_residualCubeBase n L L_inv)

/-- **Equation (8.20) support**: a residual componentwise envelope transfers to
a forward componentwise envelope by multiplying by `|L⁻¹|`. -/
theorem higham8_20_forward_componentwise_of_residual_bound (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (x xhat b Eres : Fin n → ℝ)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve : matMulVec n L x = b)
    (hres : ∀ i : Fin n, |b i - matMulVec n L xhat i| ≤ Eres i) :
    ∀ i : Fin n,
      |x i - xhat i| ≤ matMulVec n (absMatrix n L_inv) Eres i := by
  let r : Fin n → ℝ := fun k => b k - matMulVec n L xhat k
  let d : Fin n → ℝ := fun j => x j - xhat j
  have hr : r = matMulVec n L d := by
    ext i
    dsimp [r, d]
    rw [← congrFun hsolve i]
    unfold matMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmat : matMul n L_inv L = idMatrix n := by
    ext i j
    exact hLeft i j
  have hd : d = matMulVec n L_inv r := by
    rw [hr]
    ext i
    rw [← matMulVec_matMul n L_inv L d i]
    rw [hmat, matMulVec_id]
  intro i
  calc
    |x i - xhat i| = |d i| := rfl
    _ = |matMulVec n L_inv r i| := by rw [hd]
    _ ≤ ∑ j : Fin n, |L_inv i j| * |r j| :=
        abs_matMulVec_le n L_inv r i
    _ ≤ ∑ j : Fin n, |L_inv i j| * Eres j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hres j) (abs_nonneg (L_inv i j))
    _ = matMulVec n (absMatrix n L_inv) Eres i := by
        simp [matMulVec, absMatrix]

/-- **Equation (8.20) support**: normwise residual-to-forward transfer. -/
theorem higham8_20_forward_relative_infNorm_of_residual_bound (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (x xhat b Eres : Fin n → ℝ)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve : matMulVec n L x = b)
    (hres : ∀ i : Fin n, |b i - matMulVec n L xhat i| ≤ Eres i)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      infNormVec (matMulVec n (absMatrix n L_inv) Eres) / infNormVec x := by
  have hnorm :
      infNormVec (fun i => x i - xhat i) ≤
        infNormVec (matMulVec n (absMatrix n L_inv) Eres) := by
    apply infNormVec_le_of_abs_le
    · intro i
      exact le_trans
        (higham8_20_forward_componentwise_of_residual_bound
          n L L_inv x xhat b Eres hLeft hsolve hres i)
        (le_trans (le_abs_self _) (abs_le_infNormVec _ i))
    · exact infNormVec_nonneg _
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hx)

/-- **Equation (8.20), literal-executor residual-transfer form.**  This is the
fully connected all-orders conclusion obtained from the actual `(8.14)`
executor: multiply the literal residual envelope by `|L⁻¹|`.  Its envelope is
deliberately left unreduced.  The exact five-factor-to-condition-cube transfer
is proved separately below; producing the source's five-factor asymptotic
premise uses its local perturbation expansion, not a direct reduction of this
global raw envelope. -/
theorem higham8_20_fanIn7Executor_forward_from_residual_componentwise_bound
    (fp : FPModel) (n : ℕ)
    (L L_inv M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b) :
    ∀ i : Fin n,
      |higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i -
        higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i| ≤
        matMulVec n (absMatrix n L_inv)
          (matMulVec n (absMatrix n L)
            (fun k =>
              ((1 + gamma fp n) ^ 7 - 1) *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b k)) i := by
  exact higham8_20_forward_componentwise_of_residual_bound n L L_inv
    (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)
    (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) b
    (matMulVec n (absMatrix n L)
      (fun k =>
        ((1 + gamma fp n) ^ 7 - 1) *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b k))
    hLeft hsolve
    (higham8_15_fanIn7Executor_residual_componentwise_bound
      fp n L M1 M2 M3 M4 M5 M6 M7 b hn hsolve)

/-- **Equation (8.20), literal-executor relative `∞`-norm transfer form.** -/
theorem higham8_20_fanIn7Executor_forward_from_residual_relative_infNorm_bound
    (fp : FPModel) (n : ℕ)
    (L L_inv M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hn : gammaValid fp n)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve :
      matMulVec n L
        (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b)
    (hx : 0 < infNormVec
      (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)) :
    infNormVec
        (fun i =>
          higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i -
            higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b i) /
        infNormVec (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) ≤
      infNormVec
        (matMulVec n (absMatrix n L_inv)
          (matMulVec n (absMatrix n L)
            (fun k =>
              ((1 + gamma fp n) ^ 7 - 1) *
                higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b k))) /
        infNormVec (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) := by
  exact higham8_20_forward_relative_infNorm_of_residual_bound n L L_inv
    (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b)
    (higham8_14_fanIn7Executor fp n M1 M2 M3 M4 M5 M6 M7 b) b
    (matMulVec n (absMatrix n L)
      (fun k =>
        ((1 + gamma fp n) ^ 7 - 1) *
          higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b k))
    hLeft hsolve
    (higham8_15_fanIn7Executor_residual_componentwise_bound
      fp n L M1 M2 M3 M4 M5 M6 M7 b hn hsolve) hx

/-- **Equation (8.20) support**: moving the residual scalar through the final
left multiplication exposes the explicit condition-cubing matrix. -/
theorem higham8_20_condition_cube_envelope_eq (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (ρ : ℝ) (x : Fin n → ℝ) :
    matMulVec n (absMatrix n L_inv)
      (fun k =>
        ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv) (absVec n x) k) =
      fun i => ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i := by
  ext i
  calc
    matMulVec n (absMatrix n L_inv)
        (fun k =>
          ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv) (absVec n x) k) i
        =
          ρ * matMulVec n (absMatrix n L_inv)
            (matMulVec n (higham8_15_residualCubeBase n L L_inv) (absVec n x)) i := by
          unfold matMulVec
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ =
        ρ * matMulVec n
          (matMul n (absMatrix n L_inv) (higham8_15_residualCubeBase n L L_inv))
          (absVec n x) i := by
        rw [matMulVec_matMul n (absMatrix n L_inv)
          (higham8_15_residualCubeBase n L L_inv) (absVec n x) i]
    _ =
        ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i := rfl

/-- **Equation (8.20)**: if the residual has the source componentwise envelope
`ρ |L||L⁻¹||L||L⁻¹||L| |x|`, then the forward error has the condition-cubing
envelope `ρ (|L⁻¹||L|)^3 |x|`. -/
theorem higham8_20_condition_cubing_componentwise_bound (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ) (ρ : ℝ)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve : matMulVec n L x = b)
    (hres : ∀ i : Fin n,
      |b i - matMulVec n L xhat i| ≤
        ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv)
          (absVec n x) i) :
    ∀ i : Fin n,
      |x i - xhat i| ≤
        ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i := by
  have hforward :=
    higham8_20_forward_componentwise_of_residual_bound n L L_inv x xhat b
      (fun i =>
        ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv) (absVec n x) i)
      hLeft hsolve hres
  intro i
  calc
    |x i - xhat i| ≤
        matMulVec n (absMatrix n L_inv)
          (fun k =>
            ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv) (absVec n x) k) i :=
        hforward i
    _ =
        ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i := by
        rw [higham8_20_condition_cube_envelope_eq]

/-- **Equation (8.20)**, relative `∞`-norm condition-cubing form. -/
theorem higham8_20_condition_cubing_relative_infNorm_bound (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ) (ρ : ℝ)
    (hLeft : IsLeftInverse n L L_inv)
    (hsolve : matMulVec n L x = b)
    (hres : ∀ i : Fin n,
      |b i - matMulVec n L xhat i| ≤
        ρ * matMulVec n (higham8_15_residualCubeBase n L L_inv)
          (absVec n x) i)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      infNormVec
        (fun i =>
          ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i) /
        infNormVec x := by
  have hnorm :
      infNormVec (fun i => x i - xhat i) ≤
        infNormVec
          (fun i =>
            ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i) := by
    apply infNormVec_le_of_abs_le
    · intro i
      exact le_trans
        (higham8_20_condition_cubing_componentwise_bound
          n L L_inv x xhat b ρ hLeft hsolve hres i)
        (le_trans (le_abs_self _)
          (abs_le_infNormVec
            (fun i =>
              ρ * matMulVec n (higham8_20_absCondCube n L L_inv) (absVec n x) i)
            i))
    · exact infNormVec_nonneg _
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hx)

/-- **Problem 8.7(a)**: the strict row-diagonal-dominance margin of row `i`. -/
noncomputable def higham8_7_rowDiagMargin {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |A i i| - ∑ j ∈ Finset.univ.erase i, |A i j|

/-- **Problem 8.7(b)**: the positively scaled strict row-diagonal-dominance
margin of row `i`. -/
noncomputable def higham8_7_scaledRowDiagMargin {n : ℕ}
    (A : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  |A i i| * d i - ∑ j ∈ Finset.univ.erase i, |A i j| * d j

private theorem higham8_7_nonneg_sup_eq_infNormVec {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx_nonneg : ∀ i : Fin n, 0 ≤ x i) :
    Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x = infNormVec x := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (hx_nonneg ⟨0, hn⟩) (Finset.le_sup' x (Finset.mem_univ _))
  apply le_antisymm
  · rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x with
      ⟨i0, _, hδ⟩
    rw [hδ]
    simpa [abs_of_nonneg (hx_nonneg i0)] using abs_le_infNormVec x i0
  · apply infNormVec_le_of_abs_le
    · intro i
      have hle : x i ≤ δ := Finset.le_sup' x (Finset.mem_univ i)
      simpa [δ, abs_of_nonneg (hx_nonneg i)] using hle
    · exact hδ_nonneg

private theorem higham8_7_scaled_vector_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (d x : Fin n → ℝ)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNormVec x ≤
      ((Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d))) *
        infNormVec (matMulVec n A x) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  let ρ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i : Fin n => |x i| / d i)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hρ_nonneg : 0 ≤ ρ := by
    have hterm : 0 ≤ |x ⟨0, hn⟩| / d ⟨0, hn⟩ := by
      exact div_nonneg (abs_nonneg _) (le_of_lt (hd_pos _))
    exact le_trans hterm (Finset.le_sup' (fun i : Fin n => |x i| / d i) (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hx_le : ∀ i : Fin n, |x i| ≤ d i * ρ := by
    intro i
    have hi : |x i| / d i ≤ ρ :=
      Finset.le_sup' (fun j : Fin n => |x j| / d j) (Finset.mem_univ i)
    have hmul := (div_le_iff₀ (hd_pos i)).mp hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hx_norm_le : infNormVec x ≤ δ * ρ := by
    apply infNormVec_le_of_abs_le
    · intro i
      have hiδ : d i ≤ δ := Finset.le_sup' d (Finset.mem_univ i)
      calc
        |x i| ≤ d i * ρ := hx_le i
        _ ≤ δ * ρ := mul_le_mul_of_nonneg_right hiδ hρ_nonneg
    · exact mul_nonneg hδ_nonneg hρ_nonneg
  rcases Finset.exists_mem_eq_sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n => |x i| / d i) with
    ⟨i0, _, hρ⟩
  have hx_i0 : |x i0| = d i0 * ρ := by
    have hmul : ρ * d i0 = |x i0| :=
      (eq_div_iff (show d i0 ≠ 0 from (hd_pos i0).ne')).mp hρ
    simpa [mul_comm] using hmul.symm
  have hsplit :
      ∑ j : Fin n, A i0 j * x j =
        A i0 i0 * x i0 + ∑ j ∈ Finset.univ.erase i0, A i0 j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  have habs_diag :
      |A i0 i0| * |x i0| ≤
        |matMulVec n A x i0| +
          ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
    calc
      |A i0 i0| * |x i0| = |A i0 i0 * x i0| := by rw [abs_mul]
      _ = |matMulVec n A x i0 - ∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          unfold matMulVec
          rw [hsplit]
          ring_nf
      _ ≤ |matMulVec n A x i0| + |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| := by
          simpa using (abs_sub (matMulVec n A x i0)
            (∑ j ∈ Finset.univ.erase i0, A i0 j * x j))
      _ ≤ |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| := by
          have hsumabs :
              |∑ j ∈ Finset.univ.erase i0, A i0 j * x j| ≤
                ∑ j ∈ Finset.univ.erase i0, |A i0 j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
          linarith
      _ = |matMulVec n A x i0| +
            ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
  have hoff :
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j| ≤
        (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
    calc
      ∑ j ∈ Finset.univ.erase i0, |A i0 j| * |x j|
          ≤ ∑ j ∈ Finset.univ.erase i0, |A i0 j| * (d j * ρ) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hx_le j) (abs_nonneg _)
      _ = ∑ j ∈ Finset.univ.erase i0, (|A i0 j| * d j) * ρ := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
            symm
            exact Finset.sum_mul (Finset.univ.erase i0) (fun j => |A i0 j| * d j) ρ
  have hmargin_i0 :
      higham8_7_scaledRowDiagMargin A d i0 * ρ ≤ |matMulVec n A x i0| := by
    have hlin :
        |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ ≤
          |matMulVec n A x i0| := by
      have hbound :
          |A i0 i0| * |x i0| ≤
            |matMulVec n A x i0| +
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ :=
        by nlinarith [habs_diag, hoff]
      linarith
    unfold higham8_7_scaledRowDiagMargin
    calc
      (|A i0 i0| * d i0 - ∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ
          = |A i0 i0| * (d i0 * ρ) -
              (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              ring
      _ = |A i0 i0| * |x i0| -
            (∑ j ∈ Finset.univ.erase i0, |A i0 j| * d j) * ρ := by
              rw [hx_i0]
      _ ≤ |matMulVec n A x i0| := hlin
  have hβρ :
      β * ρ ≤ infNormVec (matMulVec n A x) := by
    calc
      β * ρ
          ≤ higham8_7_scaledRowDiagMargin A d i0 * ρ := by
              exact mul_le_mul_of_nonneg_right
                (Finset.inf'_le (higham8_7_scaledRowDiagMargin A d) (Finset.mem_univ i0))
                hρ_nonneg
      _ ≤ |matMulVec n A x i0| := hmargin_i0
      _ ≤ infNormVec (matMulVec n A x) := abs_le_infNormVec _ i0
  have hρ_le : ρ ≤ infNormVec (matMulVec n A x) / β := by
    exact (le_div_iff₀ hβ_pos').2 (by simpa [mul_comm] using hβρ)
  calc
    infNormVec x ≤ δ * ρ := hx_norm_le
    _ ≤ δ * (infNormVec (matMulVec n A x) / β) := by
          exact mul_le_mul_of_nonneg_left hρ_le hδ_nonneg
    _ = (δ / β) * infNormVec (matMulVec n A x) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring

/-- **Problem 8.7(b)**: a positive diagonal row scaling `D = diag(d)` with
strictly diagonally dominant rows bounds `‖A⁻¹‖∞` by `‖D‖∞ / min_i β_i`. -/
theorem higham8_7_scaledStrictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hd_pos : ∀ i : Fin n, 0 < d i)
    (hβ_pos : ∀ i : Fin n, 0 < higham8_7_scaledRowDiagMargin A d i) :
    infNorm A_inv ≤
      (Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d) /
        (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          (higham8_7_scaledRowDiagMargin A d)) := by
  let δ := Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ d
  let β := Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (higham8_7_scaledRowDiagMargin A d)
  have hδ_nonneg : 0 ≤ δ := by
    exact le_trans (le_of_lt (hd_pos ⟨0, hn⟩)) (Finset.le_sup' d (Finset.mem_univ _))
  have hβ_pos' : 0 < β := by
    rcases Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin A d) with
      ⟨i0, _, hβ⟩
    dsimp [β]
    rw [hβ]
    exact hβ_pos i0
  have hprod_nonneg : 0 ≤ δ / β := div_nonneg hδ_nonneg (le_of_lt hβ_pos')
  apply infNorm_le_of_row_sum_le
  · intro i
    let s : Fin n → ℝ := fun j => SignType.sign (A_inv i j)
    have hs_norm : infNormVec s ≤ 1 := by
      apply infNormVec_le_of_abs_le
      · intro j
        cases hsgn : SignType.sign (A_inv i j) <;> simp [s, hsgn]
      · norm_num
    have hrow_eq : matMulVec n A_inv s i = ∑ j : Fin n, |A_inv i j| := by
      unfold matMulVec s
      apply Finset.sum_congr rfl
      intro j _
      simp [self_mul_sign (A_inv i j)]
    have hprod : matMul n A A_inv = idMatrix n := by
      ext r c
      simpa [matMul, idMatrix] using hInv.2 r c
    have hAx : matMulVec n A (matMulVec n A_inv s) = s := by
      ext r
      calc
        matMulVec n A (matMulVec n A_inv s) r
            = matMulVec n (matMul n A A_inv) s r := by
                symm
                exact matMulVec_matMul n A A_inv s r
        _ = matMulVec n (idMatrix n) s r := by rw [hprod]
        _ = s r := by rw [matMulVec_id]
    have hvec :=
      higham8_7_scaled_vector_bound hn A d (matMulVec n A_inv s) hd_pos hβ_pos
    have hvec' : infNormVec (matMulVec n A_inv s) ≤ (δ / β) * infNormVec s := by
      simpa [δ, β, hAx] using hvec
    have hrow_abs : |matMulVec n A_inv s i| = ∑ j : Fin n, |A_inv i j| := by
      rw [hrow_eq]
      exact abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))
    calc
      ∑ j : Fin n, |A_inv i j| = |matMulVec n A_inv s i| := by
          symm
          exact hrow_abs
      _ ≤ infNormVec (matMulVec n A_inv s) := abs_le_infNormVec _ i
      _ ≤ (δ / β) * infNormVec s := hvec'
      _ ≤ (δ / β) * 1 := mul_le_mul_of_nonneg_left hs_norm hprod_nonneg
      _ = δ / β := by ring
  · exact hprod_nonneg

/-- **Problem 8.7(a)**: a strictly row diagonally dominant matrix satisfies
`‖A⁻¹‖∞ ≤ 1 / min_i α_i`. -/
theorem higham8_7_strictRowDiagDominant_invInfNorm_le (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hα_pos : ∀ i : Fin n, 0 < higham8_7_rowDiagMargin A i) :
    infNorm A_inv ≤
      1 / (Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_rowDiagMargin A)) := by
  simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
    using
      (higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn A A_inv
        (fun _ => 1) hInv (fun _ => by norm_num)
        (by
          intro i
          simpa [higham8_7_scaledRowDiagMargin, higham8_7_rowDiagMargin]
            using hα_pos i))

/-- **Problem 8.7(c)**: taking `D = diag(M(U)⁻¹ e)` rederives the Algorithm
8.13 upper bound `‖M(U)⁻¹ e‖∞ ≥ ‖U⁻¹‖∞`. -/
theorem higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0) :
    infNorm U_inv ≤ infNormVec (higham8_13_y M_inv) := by
  let y : Fin n → ℝ := higham8_13_y M_inv
  have habs :=
    abs_inv_le_compMatrix_inv n U U_inv M_inv hUT hU_diag hInv hM_RInv hM_inv_ut
  have hU_bound : infNorm U_inv ≤ infNorm M_inv := by
    simpa [higham8_13_mu] using higham8_13_inverse_bound_from_comparison U_inv M_inv habs
  have hM_diag_pos : ∀ i : Fin n, 0 < comparisonMatrix n U i i := by
    intro i
    simp [comparisonMatrix]
    exact hU_diag i
  have hM_offdiag : ∀ i j : Fin n, i.val < j.val → comparisonMatrix n U i j ≤ 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega)]
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    simp [comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega), hUT i j hij]
  have hM_nonneg :=
    upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
      hM_ut hM_diag_pos hM_offdiag hM_RInv hM_inv_ut
  have hM_LInv := ch7_isLeftInverse_of_isRightInverse hM_RInv
  have hM_inv_diag : ∀ i : Fin n, M_inv i i = 1 / |U i i| := by
    intro i
    have hM_inv_ut :=
      inv_upper_tri n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv
    simpa [comparisonMatrix] using
      inv_diag_entry n (comparisonMatrix n U) M_inv hM_ut
        (fun k => by simpa [comparisonMatrix] using hU_diag k) hM_LInv hM_inv_ut i
  have hy_pos : ∀ i : Fin n, 0 < y i := by
    intro i
    unfold y higham8_13_y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag_pos : 0 < M_inv i i := by
      rw [hM_inv_diag]
      exact one_div_pos.mpr (abs_pos.mpr (hU_diag i))
    have hrest_nonneg :
        0 ≤ ∑ j ∈ Finset.univ.erase i, M_inv i j := by
      exact Finset.sum_nonneg (fun j _ => hM_nonneg i j)
    linarith
  have hy_nonneg : ∀ i : Fin n, 0 ≤ y i := by
    intro i
    exact (hy_pos i).le
  have hβ_eq_one :
      ∀ i : Fin n, higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y i = 1 := by
    intro i
    unfold higham8_7_scaledRowDiagMargin y higham8_13_y
    have herase_eq :
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
            |U i j| * (∑ k : Fin n, M_inv j k) := by
      calc
        ∑ j ∈ Finset.univ.erase i, |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k)
            = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
                |comparisonMatrix n U i j| * (∑ k : Fin n, M_inv j k) := by
                  symm
                  apply Finset.sum_subset
                  · intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                    exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
                  · intro k hk hknot
                    rw [Finset.mem_erase] at hk
                    have hknot' : ¬ i.val < k.val := by
                      intro hc
                      exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
                    have hlt : k.val < i.val := by omega
                    unfold comparisonMatrix
                    simp [show i ≠ k from Fin.ne_of_val_ne (by omega), hUT i k hlt, zero_mul]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                unfold comparisonMatrix
                simp [show i ≠ j from Fin.ne_of_val_ne (by omega)]
    have hrow :=
      higham8_13_comparison_inverse_row_recurrence n U M_inv hUT hU_diag hM_RInv i
    unfold higham8_13_y at hrow
    rw [herase_eq]
    have hmain :
        |U i i| * (∑ j : Fin n, M_inv i j) -
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| * (∑ k : Fin n, M_inv j k) = 1 := by
      linarith [hrow]
    simpa [comparisonMatrix] using hmain
  have hM_bound :=
    higham8_7_scaledStrictRowDiagDominant_invInfNorm_le n hn
      (comparisonMatrix n U) M_inv y ⟨hM_LInv, hM_RInv⟩ hy_pos
      (by
        intro i
        rw [hβ_eq_one i]
        norm_num)
  have hy_sup :
      Finset.sup' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ y = infNormVec y :=
    higham8_7_nonneg_sup_eq_infNormVec hn y hy_nonneg
  have hβ_one :
      Finset.inf' Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (higham8_7_scaledRowDiagMargin (comparisonMatrix n U) y) = 1 := by
    apply Finset.inf'_eq_of_forall
    intro i _
    exact hβ_eq_one i
  have hM_bound' : infNorm M_inv ≤ infNormVec y := by
    simpa [y, hy_sup, hβ_one] using hM_bound
  exact le_trans hU_bound hM_bound'

/-! ## Problems -/

/-- **Problem 8.1 support**: no-guard subtraction-fold unroll with separate
accumulator and subtrahend perturbations from Higham model (2.6).  This is the
fold-level algebra needed for the modified Lemma 8.2 row proof. -/
theorem higham8_problem8_1_noGuard_sub_fold_unroll (fp : NoGuardFPModel)
    (m : ℕ) (a : Fin m → ℝ) (c : ℝ) :
    ∃ (α β : Fin m → ℝ),
      (∀ k, |α k| ≤ fp.u) ∧
      (∀ k, |β k| ≤ fp.u) ∧
      Fin.foldl m (fun acc t => fp.fl_sub acc (a t)) c =
        c * ∏ k : Fin m, (1 + α k) -
          ∑ t : Fin m, a t * (1 + β t) *
            ∏ k : Fin m, if t.val < k.val then (1 + α k) else 1 :=
  noGuard_sub_fold_unroll fp m a c

/-- **Problem 8.1 / modified Lemma 8.2**, scalar row form under Higham's
no-guard-digit model (2.6).  The right-hand-side term `c` is unperturbed; the
diagonal factor is bounded by `γ_(m+1)` and the zero-based `t`th product term by
`γ_(t+3)`, matching the source's one-based `θ_(i+2)` indexing. -/
theorem higham8_problem8_1_noGuard_mulSub_div_row_tight (fp : NoGuardFPModel)
    (m : ℕ) (a x : Fin m → ℝ) (c bk : ℝ) (hbk : bk ≠ 0)
    (hγ : noGuardGammaValid fp (m + 2)) :
    let fold :=
      Fin.foldl m (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) c
    ∃ (θdiag : ℝ) (η : Fin m → ℝ),
      |θdiag| ≤ noGuardGamma fp (m + 1) ∧
      (∀ t, |η t| ≤ noGuardGamma fp (t.val + 3)) ∧
      bk * fp.fl_div fold bk * (1 + θdiag) =
        c - ∑ t : Fin m, a t * x t * (1 + η t) :=
  noGuard_mulSub_div_row_tight fp m a x c bk hbk hγ

/-- **Problem 8.1 / modified Theorem 8.5**, upper-triangular no-guard
substitution: `(U + ΔU)x̂ = b`, with `|ΔU| ≤ γ_(n+1)|U|`. -/
theorem higham8_problem8_1_noGuard_backSub_backward_error (fp : NoGuardFPModel)
    (n : ℕ) (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : noGuardGammaValid fp (n + 1))
    (hrow : NoGuardBackSubSpec fp n U b xhat) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ noGuardGamma fp (n + 1) * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * xhat j = b i :=
  noGuard_backSub_backward_error fp n U b xhat hU hUT hn hrow

/-- **Problem 8.1 / modified Theorem 8.5**, lower-triangular no-guard
substitution: `(L + ΔL)x̂ = b`, with `|ΔL| ≤ γ_(n+1)|L|`. -/
theorem higham8_problem8_1_noGuard_forwardSub_backward_error (fp : NoGuardFPModel)
    (n : ℕ) (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : noGuardGammaValid fp (n + 1))
    (hrow : NoGuardForwardSubSpec fp n L b xhat) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ noGuardGamma fp (n + 1) * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * xhat j = b i :=
  noGuard_forwardSub_backward_error fp n L b xhat hL hLT hn hrow

private theorem higham8_8_matMulVec_scaledBasis {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (i : Fin n) (alpha xj : ℝ) :
    matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xj) =
      fun r => alpha * A_inv r i * xj := by
  ext r
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · simp [finiteBasisVec]
    ring
  · intro c _ hc
    simp [finiteBasisVec, hc]
  · simp

private theorem higham8_8_maxEntryNorm_pos_of_inverse {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (hInv : IsInverse n A A_inv) :
    0 < maxEntryNorm hn A_inv := by
  rcases hInv with ⟨_, hRInv⟩
  by_contra hnonpos
  have hmax_zero : maxEntryNorm hn A_inv = 0 :=
    le_antisymm (le_of_not_gt hnonpos) (maxEntryNorm_nonneg hn A_inv)
  have hentry_zero : ∀ i j : Fin n, A_inv i j = 0 := by
    intro i j
    have hle : |A_inv i j| ≤ maxEntryNorm hn A_inv :=
      entry_le_maxEntryNorm hn A_inv i j
    rw [hmax_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have h00 := hRInv ⟨0, hn⟩ ⟨0, hn⟩
  simp [hentry_zero] at h00

/-- **Problem 8.8(a)**, constructive singular rank-one perturbation.

    If `A_inv` is a right inverse of `A` and the `(j,i)` entry of `A_inv` is
    nonzero, then adding `α e_i e_jᵀ` with `α = -(A_inv j i)⁻¹` makes `A`
    singular.  This formalizes the source's possible case
    `α_ij = -(e_jᵀ A⁻¹ e_i)⁻¹`. -/
theorem higham8_8_rankOne_singular_update (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n)
    (hRInv : IsRightInverse n A A_inv)
    (hentry : A_inv j i ≠ 0) :
    Matrix.det
      (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)) = 0 := by
  classical
  let x : Fin n → ℝ := fun k => A_inv k i
  have hx_ne : x ≠ 0 := by
    intro hx
    exact hentry (congr_fun hx j)
  have hAx : ∀ r : Fin n, Matrix.mulVec (Matrix.of A) x r =
      if r = i then 1 else 0 := by
    intro r
    simpa [Matrix.mulVec, dotProduct, x] using hRInv r i
  have hmul :
      Matrix.mulVec
        (Matrix.of A + Matrix.single i j (-(A_inv j i)⁻¹)) x = 0 := by
    ext r
    by_cases hri : r = i
    · subst r
      simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x]
      field_simp [hentry]
      norm_num
    · simp [Matrix.add_mulVec, Matrix.single_mulVec, hAx, x, hri]
  exact
    (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A +
        Matrix.single i j (-(A_inv j i)⁻¹)))).mp
      ⟨x, hx_ne, hmul⟩

/-- **Problem 8.8(a)**, converse singularity condition for a single-entry
rank-one perturbation.

    If `A + α e_i e_jᵀ` is singular, then necessarily
    `1 + α (A⁻¹)_{j i} = 0`. -/
theorem higham8_8_rankOne_singular_update_den_eq_zero (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    1 + alpha * A_inv j i = 0 := by
  classical
  rcases hInv with ⟨hLInv, _⟩
  rcases (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A + Matrix.single i j alpha))).mpr hsing with
    ⟨x, hx_ne, hmul⟩
  have hmul' := hmul
  rw [Matrix.add_mulVec, Matrix.single_mulVec] at hmul'
  have hAx : matMulVec n A x = fun r => -alpha * finiteBasisVec i r * x j := by
    ext r
    have hr := congrFun hmul' r
    by_cases hri : r = i
    · subst r
      have hr0 : matMulVec n A x i + alpha * x j = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec] using hr
      have hrow : matMulVec n A x i = -alpha * x j := by
        linarith
      simpa [finiteBasisVec] using hrow
    · have hr0 : matMulVec n A x r = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec, hri] using hr
      simpa [finiteBasisVec, hri] using hr0
  have hprod : matMul n A_inv A = idMatrix n := by
    ext r c
    simpa [matMul] using hLInv r c
  have hxrepr : x = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) := by
    ext r
    calc
      x r = matMulVec n (idMatrix n) x r := by rw [matMulVec_id]
      _ = matMulVec n (matMul n A_inv A) x r := by rw [hprod]
      _ = matMulVec n A_inv (matMulVec n A x) r := by
            exact matMulVec_matMul n A_inv A x r
      _ = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) r := by
            rw [hAx]
  have hxformula : ∀ r : Fin n, x r = -alpha * A_inv r i * x j := by
    intro r
    have hr := congrFun hxrepr r
    rw [higham8_8_matMulVec_scaledBasis A_inv i (-alpha) (x j)] at hr
    simpa [mul_assoc, mul_left_comm, mul_comm] using hr
  by_contra hden
  have hcoef : (1 + alpha * A_inv j i) * x j = 0 := by
    have hj := hxformula j
    nlinarith
  have hxj_zero : x j = 0 := by
    rcases mul_eq_zero.mp hcoef with hzero | hzero
    · exact False.elim (hden hzero)
    · exact hzero
  have hx_zero : x = 0 := by
    ext r
    rw [hxformula r, hxj_zero]
    simp
  exact hx_ne hx_zero

/-- **Problem 8.8(a)**, exact solvability criterion:
`A + α e_i e_jᵀ` is singular exactly when
`α = -(A⁻¹)_{j i}^{-1}` and `(A⁻¹)_{j i} ≠ 0`. -/
theorem higham8_8_rankOne_singular_update_iff (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv) :
    Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 ↔
      A_inv j i ≠ 0 ∧ alpha = -(A_inv j i)⁻¹ := by
  constructor
  · intro hsing
    have hden :=
      higham8_8_rankOne_singular_update_den_eq_zero n A A_inv i j alpha hInv hsing
    have hentry : A_inv j i ≠ 0 := by
      intro hzero
      simp [hzero] at hden
    refine ⟨hentry, ?_⟩
    rw [inv_eq_one_div]
    have hprod : alpha * A_inv j i = -1 := by
      linarith [hden]
    have halpha : alpha = -1 / A_inv j i := (eq_div_iff hentry).2 hprod
    simpa [div_eq_mul_inv] using halpha
  · intro h
    rcases hInv with ⟨_, hRInv⟩
    rcases h with ⟨hentry, halpha⟩
    simpa [halpha] using
      higham8_8_rankOne_singular_update n A A_inv i j hRInv hentry

/-- **Problem 8.8(a)**, source magnitude formula for a singular single-entry
perturbation. -/
theorem higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    |alpha| = |A_inv j i|⁻¹ := by
  rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
    ⟨hentry, halpha⟩
  rw [halpha, abs_neg, abs_inv]

/-- **Problem 8.8(a)**, source "best place" criterion:
if `|(A⁻¹)_{r s}|` is maximal, then perturbing the `(s,r)` entry gives the
smallest-magnitude singular rank-one update. -/
theorem higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (r s : Fin n)
    (hInv : IsInverse n A A_inv)
    (hmax : |A_inv r s| = maxEntryNorm hn A_inv) :
    Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      ∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha| := by
  have hmax_pos : 0 < maxEntryNorm hn A_inv :=
    higham8_8_maxEntryNorm_pos_of_inverse hn A A_inv hInv
  have hrs_pos : 0 < |A_inv r s| := by
    rw [hmax]
    exact hmax_pos
  have hrs : A_inv r s ≠ 0 := abs_pos.mp hrs_pos
  refine ⟨?_, ?_⟩
  · rcases hInv with ⟨_, hRInv⟩
    simpa using
      higham8_8_rankOne_singular_update n A A_inv s r hRInv hrs
  · intro i j alpha hsing
    rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
      ⟨hentry, halpha⟩
    have hentry_le : |A_inv j i| ≤ |A_inv r s| := by
      rw [hmax]
      exact entry_le_maxEntryNorm hn A_inv j i
    have hentry_pos : 0 < |A_inv j i| := abs_pos.mpr hentry
    calc
      |-(A_inv r s)⁻¹| = |A_inv r s|⁻¹ := by
        rw [abs_neg, abs_inv]
      _ ≤ |A_inv j i|⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hentry_pos hentry_le
      _ = |alpha| := by
        symm
        exact higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry
          n A A_inv i j alpha hInv hsing

/-- **Problem 8.8(a)**, existence form of the Appendix A "best place" answer.

    For a nonsingular matrix, there is an inverse entry of maximal absolute
    value, and perturbing the transposed position yields a singular rank-one
    update of smallest possible magnitude. -/
theorem higham8_8_bestRankOneSingularUpdate_exists (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv) :
    ∃ r s : Fin n,
      |A_inv r s| = maxEntryNorm hn A_inv ∧
      Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      (∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha|) := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let rowMax : Fin n → ℝ :=
    fun r => Finset.sup' Finset.univ hne (fun s => |A_inv r s|)
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' hne rowMax
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne (fun s => |A_inv r s|)
  have hmax : |A_inv r s| = maxEntryNorm hn A_inv := by
    calc
      |A_inv r s| = rowMax r := hs.symm
      _ = maxEntryNorm hn A_inv := by
            simpa [rowMax, maxEntryNorm] using hr.symm
  refine ⟨r, s, hmax, ?_, ?_⟩
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).1
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).2

/-- **Problem 8.8(b)**: the stress matrix `T_n = U(1)` is made singular by a
rank-one update in the `(n,1)` position with
`α = -2^(2-n) = -((2^(n-2))⁻¹)`. -/
theorem higham8_8b_stressUpper_lastFirst_singular_update (n : ℕ) (h2 : 1 < n) :
    Matrix.det
      (Matrix.of (higham8_3_stressUpper n 1) +
        Matrix.single ⟨n - 1, by omega⟩ ⟨0, by omega⟩
          (-((2 : ℝ) ^ (n - 2))⁻¹)) = 0 := by
  let last : Fin n := ⟨n - 1, by omega⟩
  let first : Fin n := ⟨0, by omega⟩
  have hInv := higham8_4_stressUpperInvFormula_isInverse n 1
  have hlt : first.val < last.val := by
    dsimp [first, last]
    omega
  have hne : first ≠ last := Fin.ne_of_val_ne (by
    dsimp [first, last]
    omega)
  have hsub : n - 1 - 1 = n - 2 := by
    omega
  have hpow_two : (1 + 1 : ℝ) ^ (n - 2) = (2 : ℝ) ^ (n - 2) := by
    norm_num
  have hentry_eq :
      higham8_4_stressUpperInvFormula n 1 first last = (2 : ℝ) ^ (n - 2) := by
    simp [higham8_4_stressUpperInvFormula, first, last, hlt, hne, hsub, hpow_two]
  have hentry : higham8_4_stressUpperInvFormula n 1 first last ≠ 0 := by
    rw [hentry_eq]
    positivity
  have hs :=
    higham8_8_rankOne_singular_update n
      (higham8_3_stressUpper n 1)
      (higham8_4_stressUpperInvFormula n 1)
      last first hInv.2 hentry
  simpa [first, last, higham8_4_stressUpperInvFormula, hlt, hne, hsub, hpow_two] using hs

end NumStability
