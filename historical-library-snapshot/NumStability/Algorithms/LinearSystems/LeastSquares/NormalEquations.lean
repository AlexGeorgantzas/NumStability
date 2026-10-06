import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators
open scoped BigOperators Matrix.Norms.Frobenius

/-!
# NormalEquations

Canonical reusable module extracted without change from LSNormalEquations, LSQRSolve.
-/

/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 386:
    the 2-by-2 normal-equations cross-product example
    `A = [[1, 1], [epsilon, 0]]`. -/
noncomputable def normalEquationsCrossProductExampleA
    (epsilon : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 then 1 else if j = 0 then epsilon else 0
/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    exact cross product for the example
    `A^T A = [[1 + epsilon^2, 1], [1, 1]]`. -/
theorem normalEquationsCrossProductExample_gram_eq (epsilon : ℝ) :
    (fun i j : Fin 2 =>
        ∑ k : Fin 2,
          normalEquationsCrossProductExampleA epsilon k i *
          normalEquationsCrossProductExampleA epsilon k j) =
      fun i j =>
        if i = 0 then
          if j = 0 then 1 + epsilon ^ 2 else 1
        else
          if j = 0 then 1 else 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [normalEquationsCrossProductExampleA]
    ring
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]
/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    source model of the rounded cross product in the example,
    `fl(A^T A) = [[1, 1], [1, 1]]`. -/
noncomputable def normalEquationsCrossProductExampleRoundedGram :
    Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1
/-- The rounded cross product displayed in Higham's Section 20.4 example is
    singular, witnessed by the nonzero vector `[1, -1]`. -/
theorem normalEquationsCrossProductExampleRoundedGram_singular :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2 normalEquationsCrossProductExampleRoundedGram x = 0 := by
  refine ⟨fun i => if i = 0 then 1 else -1, ?_, ?_⟩
  · intro hx
    have h0 := congrFun hx (0 : Fin 2)
    norm_num at h0
  · ext i
    fin_cases i <;>
      norm_num [matMulVec, normalEquationsCrossProductExampleRoundedGram]
/-- Computed solution vector produced by the normal-equations Cholesky solve
    used in `ls_normal_equations_backward`. -/
noncomputable def normalEqCholeskyXHat (fp : FPModel) (n : ℕ)
    (c_hat : Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n R_hat
    (fl_forwardSub fp n (fun i j : Fin n => R_hat j i) c_hat)
/-- The rectangular normal equations for a least-squares instance.  A
    rectangular QR backward-error theorem usually says the computed solution is
    the exact least-squares solution for perturbed data; this predicate is the
    normal-equation form of that exactness. -/
def RectLSNormalEquations {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x_hat : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, matMulVec n (rectLSGram A) x_hat j = rectLSRhs A b j
private theorem rectLSNormalEquations_residual_sum_eq_diff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (j : Fin n) :
    ∑ i : Fin m, A i j * lsResidual A b x i =
      (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) -
        ∑ i : Fin m, A i j * b i := by
  calc
    ∑ i : Fin m, A i j * lsResidual A b x i
        = ∑ i : Fin m, A i j * rectMatMulVec A x i -
            ∑ i : Fin m, A i j * b i := by
          simp_rw [lsResidual, mul_sub]
          rw [Finset.sum_sub_distrib]
    _ = (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) -
        ∑ i : Fin m, A i j * b i := by
          congr 1
          calc
            ∑ i : Fin m, A i j * rectMatMulVec A x i
                = ∑ i : Fin m, ∑ k : Fin n, A i j * (A i k * x k) := by
                  unfold rectMatMulVec
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
            _ = ∑ k : Fin n, ∑ i : Fin m, A i j * (A i k * x k) := by
                  rw [Finset.sum_comm]
            _ = ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k := by
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
/-- The rectangular normal equations are equivalent to the residual being
    orthogonal to every column of `A`; used to connect the augmented systems in
    (20.3)-(20.4) with exact least-squares minimizers. -/
theorem RectLSNormalEquations.iff_residual_orthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    RectLSNormalEquations A b x ↔
      ∀ j : Fin n, ∑ i : Fin m, A i j * lsResidual A b x i = 0 := by
  constructor
  · intro h j
    have hj := h j
    unfold rectLSGram rectLSRhs matMulVec at hj
    rw [rectLSNormalEquations_residual_sum_eq_diff A b x j, hj]
    ring
  · intro h j
    unfold rectLSGram rectLSRhs matMulVec
    have hdiff : (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) -
        ∑ i : Fin m, A i j * b i = 0 := by
      rw [← rectLSNormalEquations_residual_sum_eq_diff A b x j]
      exact h j
    exact sub_eq_zero.mp hdiff
/-- Normal-equation solutions have residuals orthogonal to the data columns. -/
theorem RectLSNormalEquations.residual_orthogonal {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (h : RectLSNormalEquations A b x) :
    ∀ j : Fin n, ∑ i : Fin m, A i j * lsResidual A b x i = 0 :=
  (RectLSNormalEquations.iff_residual_orthogonal A b x).mp h
/-- A residual orthogonal to every data column satisfies the rectangular normal
    equations. -/
theorem RectLSNormalEquations.of_residual_orthogonal {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (h : ∀ j : Fin n, ∑ i : Fin m, A i j * lsResidual A b x i = 0) :
    RectLSNormalEquations A b x :=
  (RectLSNormalEquations.iff_residual_orthogonal A b x).mpr h
/-- Concrete full-column-rank pseudoinverse table `(A^T A)^{-1} A^T`,
    using the repository nonsingular inverse candidate for `A^T A`. -/
noncomputable def lsAplusOfGramNonsingInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin m → ℝ :=
  fun j i => ∑ k : Fin n, lsGramNonsingInv A j k * A i k
/-- Full-column-rank Gram pseudoinverse support: the range projection
    `A(AᵀA)^{-1}Aᵀ` is symmetric. -/
theorem lsAplusOfGramNonsingInv_projection_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectMatMul A (lsAplusOfGramNonsingInv A)) := by
  intro i j
  unfold rectMatMul lsAplusOfGramNonsingInv
  calc
    (∑ k : Fin n, A i k *
        (∑ l : Fin n, lsGramNonsingInv A k l * A j l)) =
        ∑ k : Fin n, ∑ l : Fin n,
          A i k * (lsGramNonsingInv A k l * A j l) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
    _ = ∑ l : Fin n, ∑ k : Fin n,
          A i k * (lsGramNonsingInv A k l * A j l) := by
          rw [Finset.sum_comm]
    _ = ∑ l : Fin n, ∑ k : Fin n,
          A j l * (lsGramNonsingInv A l k * A i k) := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro k _
          rw [lsGramNonsingInv_symmetric A k l]
          ring
    _ = ∑ l : Fin n, A j l *
          (∑ k : Fin n, lsGramNonsingInv A l k * A i k) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]
private theorem sum_smul_finiteBasisVec_mul {n : ℕ}
    (j : Fin n) (t : ℝ) (c : Fin n → ℝ) :
    (∑ k : Fin n, (t * finiteBasisVec j k) * c k) = t * c j := by
  unfold finiteBasisVec
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))
private theorem linear_term_eq_zero_of_quadratic_nonneg
    {a c : ℝ} (ha : 0 ≤ a)
    (hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a) :
    c = 0 := by
  by_contra hc
  let t : ℝ := -c / (a + 1)
  have hden_pos : 0 < a + 1 := by linarith
  have hden_ne : a + 1 ≠ 0 := ne_of_gt hden_pos
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hcalc :
      2 * t * c + t ^ 2 * a =
        -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
    dsimp [t]
    field_simp [hden_ne]
    ring
  have hnum_pos : 0 < c ^ 2 * (a + 2) := by nlinarith
  have hden_sq_pos : 0 < (a + 1) ^ 2 := sq_pos_of_pos hden_pos
  have hneg : -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hnum_pos) hden_sq_pos
  have ht := hquad t
  rw [hcalc] at ht
  linarith
/-- The rectangular normal equations characterize an exact minimizer of the
    squared least-squares objective. -/
theorem RectLSNormalEquations.isLeastSquaresMinimizer {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (h : RectLSNormalEquations A b x) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  let d : Fin n → ℝ := fun j => y j - x j
  have hy : y = fun j => x j + d j := by
    ext j
    dsimp [d]
    ring
  have horth := h.residual_orthogonal
  have hcross :
      (∑ j : Fin n, d j *
        (∑ i : Fin m, A i j * lsResidual A b x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [horth j]
    ring
  have hexp := lsObjective_add_direction_eq A b x d
  rw [← hy] at hexp
  rw [hexp, hcross]
  have hnonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A d) :=
    vecNorm2Sq_nonneg (rectMatMulVec A d)
  nlinarith
/-- Every exact minimizer of the squared least-squares objective satisfies the
    rectangular normal equations. -/
theorem IsLeastSquaresMinimizer.rectLSNormalEquations {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (hmin : IsLeastSquaresMinimizer A b x) :
    RectLSNormalEquations A b x := by
  apply RectLSNormalEquations.of_residual_orthogonal
  intro j
  let c : ℝ := ∑ i : Fin m, A i j * lsResidual A b x i
  let a : ℝ := vecNorm2Sq (rectMatMulVec A (finiteBasisVec j))
  have ha : 0 ≤ a := by
    dsimp [a]
    exact vecNorm2Sq_nonneg (rectMatMulVec A (finiteBasisVec j))
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a := by
    intro t
    let d : Fin n → ℝ := fun k => t * finiteBasisVec j k
    have hobj := hmin (fun k => x k + d k)
    have hexp := lsObjective_add_direction_eq A b x d
    have hcross :
        (∑ k : Fin n, d k *
          (∑ i : Fin m, A i k * lsResidual A b x i)) = t * c := by
      dsimp [d, c]
      exact sum_smul_finiteBasisVec_mul j t
        (fun k => ∑ i : Fin m, A i k * lsResidual A b x i)
    have hnorm : vecNorm2Sq (rectMatMulVec A d) = t ^ 2 * a := by
      dsimp [d, a]
      rw [rectMatMulVec_smul, vecNorm2Sq_smul]
    rw [hexp, hcross, hnorm] at hobj
    nlinarith
  exact linear_term_eq_zero_of_quadratic_nonneg ha hquad
/-- Exact minimizers of `||A x - b||₂²` are exactly the solutions of the normal
    equations. -/
theorem RectLSNormalEquations.iff_isLeastSquaresMinimizer {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    RectLSNormalEquations A b x ↔ IsLeastSquaresMinimizer A b x := by
  constructor
  · intro h
    exact h.isLeastSquaresMinimizer
  · intro h
    exact h.rectLSNormalEquations
/-- Higham, 2nd ed., Chapter 20, Theorem 20.3 deterministic endgame:
    once a computed vector satisfies the normal equations for perturbed
    rectangular data, it is the exact least-squares minimizer for that
    perturbed data.  This is the source-facing bridge from a future concrete
    QR backward-error theorem to the book's "exact LS solution" conclusion. -/
theorem RectLSNormalEquations.perturbed_isLeastSquaresMinimizer {m n : ℕ}
    {A ΔA : Fin m → Fin n → ℝ} {b Δb : Fin m → ℝ}
    {x_hat : Fin n → ℝ}
    (hNE : RectLSNormalEquations
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i) x_hat) :
    IsLeastSquaresMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i) x_hat :=
  hNE.isLeastSquaresMinimizer
/-- A solution of the column-permuted normal equations maps back to a solution
    of the original normal equations by the inverse coefficient permutation. -/
theorem RectLSNormalEquations.of_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x_hat : Fin n → ℝ)
    (h : RectLSNormalEquations (rectPermuteCols π A) b x_hat) :
    RectLSNormalEquations A b (vecPermute π.symm x_hat) := by
  intro j
  have hj := h (π.symm j)
  unfold RectLSNormalEquations at hj
  unfold matMulVec rectLSGram rectLSRhs at hj
  unfold rectPermuteCols at hj
  unfold matMulVec rectLSGram rectLSRhs vecPermute
  calc
    ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x_hat (π.symm k)
        = ∑ k : Fin n, (∑ i : Fin m, A i j * A i (π k)) * x_hat k := by
            exact
              (Fintype.sum_equiv π
                (fun k : Fin n =>
                  (∑ i : Fin m, A i j * A i (π k)) * x_hat k)
                (fun k : Fin n =>
                  (∑ i : Fin m, A i j * A i k) * x_hat (π.symm k))
                (fun k => by simp)).symm
    _ = ∑ i : Fin m, A i j * b i := by
            simpa using hj
/-- A solution of row-sorted and column-pivoted normal equations maps back to
    a solution of the original normal equations by undoing the column
    permutation. -/
theorem RectLSNormalEquations.of_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x_hat : Fin n → ℝ)
    (h : RectLSNormalEquations
      (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x_hat) :
    RectLSNormalEquations A b (vecPermute π.symm x_hat) := by
  apply RectLSNormalEquations.of_permuteCols π A b x_hat
  intro j
  have hj := h j
  simpa [rectLSGram_permuteRows, rectLSRhs_permuteRows] using hj
/-- A rowwise normal-equation identity implies the rectangular normal
    equations.  This is useful for QR handoffs: rows in a zero lower block do
    not need zero transformed right-hand side, because they are multiplied by
    zero rows of the transformed matrix. -/
theorem RectLSNormalEquations.of_rowwise_normal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x_hat : Fin n → ℝ)
    (hrow : ∀ (i : Fin m) (j : Fin n),
      A i j * (∑ k : Fin n, A i k * x_hat k) = A i j * b i) :
    RectLSNormalEquations A b x_hat := by
  intro j
  unfold rectLSGram rectLSRhs matMulVec
  calc
    ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x_hat k
        = ∑ k : Fin n, ∑ i : Fin m, (A i j * A i k) * x_hat k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ k : Fin n, (A i j * A i k) * x_hat k := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, A i j * (∑ k : Fin n, A i k * x_hat k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ i : Fin m, A i j * b i := by
            apply Finset.sum_congr rfl
            intro i _
            exact hrow i j
/-- Exact top-block solve plus a zero lower matrix block supplies the
    rectangular normal equations for transformed QR data.

    In a tall QR least-squares solve, after applying the orthogonal
    transformations one has `Qᵀ A = [R; 0]` and `Qᵀ b = [c; d]`.  If the
    computed solution solves the top square system `R x = c`, then it satisfies
    the normal equations for the whole transformed rectangular problem.  The
    lower transformed right-hand side `d` is unrestricted. -/
theorem RectLSNormalEquations.of_top_solve_zero_bottom {m n : ℕ}
    (A_hat : Fin m → Fin n → ℝ) (b_hat : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (c : Fin n → ℝ) (x_hat : Fin n → ℝ)
    (hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_hat i j = R ⟨i.val, hi⟩ j)
    (hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat i j = 0)
    (hb_top : ∀ (i : Fin m) (hi : i.val < n),
      b_hat i = c ⟨i.val, hi⟩)
    (hsolve : ∀ r : Fin n, matMulVec n R x_hat r = c r) :
    RectLSNormalEquations A_hat b_hat x_hat := by
  apply RectLSNormalEquations.of_rowwise_normal
  intro i j
  by_cases hi : i.val < n
  · have hdot :
        (∑ k : Fin n, A_hat i k * x_hat k) = b_hat i := by
      calc
        ∑ k : Fin n, A_hat i k * x_hat k
            = ∑ k : Fin n, R ⟨i.val, hi⟩ k * x_hat k := by
                apply Finset.sum_congr rfl
                intro k _
                rw [hA_top i k hi]
        _ = matMulVec n R x_hat ⟨i.val, hi⟩ := rfl
        _ = c ⟨i.val, hi⟩ := hsolve ⟨i.val, hi⟩
        _ = b_hat i := (hb_top i hi).symm
    rw [hdot]
  · have hAij : A_hat i j = 0 := hA_bottom i j (le_of_not_gt hi)
    rw [hAij, zero_mul, zero_mul]
/-- A floating-point back substitution theorem supplies an exact perturbed
    top-block solve, hence rectangular normal equations for the corresponding
    perturbed transformed QR data.

    This closes the triangular-solve handoff part of the rectangular QR route:
    it still assumes a future concrete QR theorem supplies the transformed
    top-block shape and the transformed right-hand side. -/
theorem RectLSNormalEquations.exists_topBlock_of_fl_backSub {m n : ℕ}
    (fp : FPModel) (R : Fin n → Fin n → ℝ) (c : Fin n → ℝ)
    (b_hat : Fin m → ℝ)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n)
    (hb_top : ∀ (i : Fin m) (hi : i.val < n),
      b_hat i = c ⟨i.val, hi⟩) :
    ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔR i j| ≤ gamma fp n * |R i j|) ∧
      RectLSNormalEquations
        (rectTopBlock (fun i j => R i j + ΔR i j)) b_hat
        (fl_backSub fp n R c) := by
  rcases backSub_backward_error fp n R c hdiag hupper hγ with
    ⟨ΔR, hΔR, hsolve⟩
  refine ⟨ΔR, hΔR, ?_⟩
  exact
    RectLSNormalEquations.of_top_solve_zero_bottom
      (rectTopBlock (fun i j => R i j + ΔR i j)) b_hat
      (fun i j => R i j + ΔR i j) c (fl_backSub fp n R c)
      (fun i j hi => rectTopBlock_top (fun i j => R i j + ΔR i j) i j hi)
      (fun i j hi => rectTopBlock_bottom (fun i j => R i j + ΔR i j) i j hi)
      hb_top
      (fun r => by simpa [matMulVec] using hsolve r)
/-- Exact least-squares normal equations are invariant under an orthogonal
    row transformation of both the matrix and right-hand side. -/
theorem RectLSNormalEquations.of_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin n → ℝ)
    (b b_hat : Fin m → ℝ) (x_hat : Fin n → ℝ)
    (hU : IsOrthogonal m U)
    (hAhat : A_hat = matMulRectLeft U A)
    (hbhat : b_hat = matMulVec m U b)
    (hNE : RectLSNormalEquations A_hat b_hat x_hat) :
    RectLSNormalEquations A b x_hat := by
  intro j
  have hG := rectLSGram_matMulRectLeft_orthogonal U A hU
  have hg := rectLSRhs_matMulRectLeft_orthogonal U A b hU
  have hNE' : matMulVec n (rectLSGram (matMulRectLeft U A)) x_hat j =
      rectLSRhs (matMulRectLeft U A) (matMulVec m U b) j := by
    simpa [hAhat, hbhat] using hNE j
  simpa [hG, hg] using hNE'

end NumStability
