import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# BackwardError

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- **Theorem 20.3** (Higham, 2nd ed., Chapter 20, Section 20.2):
    Householder QR least squares backward stability.

    The computed LS solution x̂ via Householder QR is the exact LS
    minimizer of min_x ‖(b + Δb) − (A + ΔA)x‖₂ where
    ‖ΔA‖_F ≤ c · ‖A‖_F and ‖Δb‖₂ ≤ c · ‖b‖₂ with c = nγ̃_{cm}.

    Since the rectangular A ∈ ℝ^{m×n} is not representable in the
    library's square-matrix framework, we capture the consequence
    for the n×n Gram system: the perturbed normal equations
    (A+ΔA)ᵀ(A+ΔA)x̂ = (A+ΔA)ᵀ(b+Δb) hold, which projects to
    a perturbation of the Gram system AᵀAx = Aᵀb.

    We package this as a structure, paralleling the library's
    treatment of `HouseholderQRBackwardError` and `QRSolveBackwardError`.

    The proof is described by Higham as a straightforward generalization of
    the QR-factorization proof in the preceding chapter. -/
structure LSQRSolveBackwardError (n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb x_hat : Fin n → ℝ)
    (c_G c_g : ℝ) : Prop where
  /-- There exist perturbations ΔG, Δg to the Gram system such that
      (AᵀA + ΔG)x̂ = Aᵀb + Δg with bounded perturbations. -/
  result : ∃ (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ),
    (∀ i, matMulVec n (fun a b => ATA a b + ΔG a b) x_hat i = ATb i + Δg i) ∧
    frobNorm ΔG ≤ c_G ∧
    (∀ i, |Δg i| ≤ c_g)
/-- If the induced perturbations from a rectangular backward-error statement
    satisfy the local Gram/RHS radii, then they give the repository's
    `LSQRSolveBackwardError` specification.  The remaining hard foundation is
    to prove those perturbations and radii for a concrete rectangular QR or
    preconditioned least-squares algorithm. -/
theorem LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations
    {m n : ℕ} (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (x_hat : Fin n → ℝ) (c_G c_g : ℝ)
    (hNE : RectLSNormalEquations
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i) x_hat)
    (hG : frobNorm (rectLSGramPerturbation A ΔA) ≤ c_G)
    (hg : ∀ j : Fin n, |rectLSRhsPerturbation A b ΔA Δb j| ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b) x_hat c_G c_g := by
  refine ⟨rectLSGramPerturbation A ΔA, rectLSRhsPerturbation A b ΔA Δb, ?_, hG, hg⟩
  exact rectLSNormalEquations_perturbed_to_gram_system A ΔA b Δb x_hat hNE
/-- A rectangular perturbed-normal-equation theorem plus normwise rectangular
    data perturbation bounds feeds the local QR specification whenever the
    induced norm budgets fit inside the requested Gram/RHS radii.  This is the
    final algebraic handoff expected from a future concrete rectangular QR or
    preconditioner backward-error theorem. -/
theorem LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget
    {m n : ℕ} (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (x_hat : Fin n → ℝ) (cA cb c_G c_g : ℝ)
    (hNE : RectLSNormalEquations
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i) x_hat)
    (hΔA : frobNorm ΔA ≤ cA) (hΔb : vecNorm2 Δb ≤ cb)
    (hG : frobNorm (rectLSGramPerturbationNormBudget A cA) ≤ c_G)
    (hg : ∀ j : Fin n, rectLSRhsPerturbationNormBudget A b cA cb j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b) x_hat c_G c_g := by
  have hcA : 0 ≤ cA := (frobNorm_nonneg ΔA).trans hΔA
  have hG' : frobNorm (rectLSGramPerturbation A ΔA) ≤ c_G :=
    (rectLSGramPerturbation_frobNorm_le_normBudget A ΔA hcA hΔA).trans hG
  have hg' :
      ∀ j : Fin n, |rectLSRhsPerturbation A b ΔA Δb j| ≤ c_g := by
    intro j
    exact (rectLSRhsPerturbation_abs_le_normBudget A b ΔA Δb hΔA hΔb j).trans (hg j)
  exact LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations
    A ΔA b Δb x_hat c_G c_g hNE hG' hg'
/-- Common-`Q` transformed QR data, a rounded top-block solve, and norm-budget
    hypotheses imply the local least-squares QR backward-error specification.

    This is the specification-level version of the rectangular QR route: a
    future concrete Householder/preconditioner theorem only has to provide the
    common transformed data, `[R;0]` shape, and the input perturbation radii
    appearing here. -/
theorem LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget
    {m n : ℕ} (fp : FPModel)
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (A_hat : Fin m → Fin n → ℝ) (b_hat : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (cTop : Fin n → ℝ)
    (cA0 cb c_G c_g : ℝ)
    (hQ : IsOrthogonal m Q)
    (hAhat : ∀ i j, A_hat i j =
      matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (hbhat : ∀ i, b_hat i =
      matMulVec m (matTranspose Q) (fun a => b a + Δb a) i)
    (hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_hat i j = R ⟨i.val, hi⟩ j)
    (hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat i j = 0)
    (hb_top : ∀ (i : Fin m) (hi : i.val < n),
      b_hat i = cTop ⟨i.val, hi⟩)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n)
    (hΔA : frobNormRect ΔA ≤ cA0)
    (hΔb : vecNorm2 Δb ≤ cb)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (cA0 + gamma fp n * frobNormRect (rectTopBlock (m := m) R))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (cA0 + gamma fp n * frobNormRect (rectTopBlock (m := m) R)) cb j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R cTop) c_G c_g := by
  rcases
    RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound
      (m := m) (n := n) fp A ΔA b Δb A_hat b_hat Q R cTop
      hQ hAhat hbhat hA_top hA_bottom hb_top hdiag hupper hγ with
    ⟨ΔR, ΔA_total, _hΔR, hNE, hΔA_total_rect⟩
  let cA : ℝ :=
    cA0 + gamma fp n * frobNormRect (rectTopBlock (m := m) R)
  have hΔA_total_rect_to_cA : frobNormRect ΔA_total ≤ cA := by
    calc
      frobNormRect ΔA_total
          ≤ frobNormRect ΔA +
              gamma fp n * frobNormRect (rectTopBlock (m := m) R) := hΔA_total_rect
      _ ≤ cA0 + gamma fp n * frobNormRect (rectTopBlock (m := m) R) := by
            exact add_le_add hΔA (le_refl _)
      _ = cA := rfl
  have hΔA_total : frobNorm ΔA_total ≤ cA := by
    rw [← frobNormRect_eq_frobNormFn]
    exact hΔA_total_rect_to_cA
  exact
    LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget
      (m := m) (n := n) A ΔA_total b Δb (fl_backSub fp n R cTop)
      cA cb c_G c_g hNE hΔA_total hΔb
      (by simpa [cA] using hG)
      (by intro j; simpa [cA] using hg j)
/-- Supplied rectangular orthogonal-transformation QR route into the local
    least-squares QR backward-error specification.

    This theorem composes the common matrix/right-hand-side accumulation
    theorem, the rounded top-block solve, the gamma top-block norm budget, and
    the rectangular induced Gram/RHS norm-budget adapter.  It is not yet a
    concrete Householder implementation theorem: it assumes the step
    recurrences, the final `[R;0]` transformed shape, and the transformed top
    right-hand side. -/
theorem LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget
    {m n r : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P ΔP : ℕ → Fin m → Fin m → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (R : Fin n → Fin n → ℝ) (cTop : Fin n → ℝ)
    (c_G c_g : ℝ)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hP : ∀ k, k < r → IsOrthogonal m (P k))
    (hΔP : ∀ k, k < r → frobNorm (ΔP k) ≤ cStep)
    (hNextA : ∀ k, k < r →
      A_hat (k + 1) = matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k))
    (hNextb : ∀ k, k < r →
      b_hat (k + 1) = matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k))
    (hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_hat r i j = R ⟨i.val, hi⟩ j)
    (hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat r i j = 0)
    (hb_top : ∀ (i : Fin m) (hi : i.val < n),
      b_hat r i = cTop ⟨i.val, hi⟩)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ r - 1) * frobNormRect A +
            gamma fp n * frobNormRect (rectTopBlock (m := m) R))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ r - 1) * frobNormRect A +
            gamma fp n * frobNormRect (rectTopBlock (m := m) R))
          (((1 + cStep) ^ r - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R cTop) c_G c_g := by
  rcases
    rect_orthogonal_matrix_vector_sequence_geometric
      m n r A b A_hat b_hat P ΔP cStep hcStep hInitA hInitb
      hP hΔP hNextA hNextb with
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA, hΔb⟩
  exact
    LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget
      (m := m) (n := n) fp A ΔA b Δb (A_hat r) (b_hat r) Q R cTop
      (((1 + cStep) ^ r - 1) * frobNormRect A)
      (((1 + cStep) ^ r - 1) * vecNorm2 b)
      c_G c_g hQ hArep hbrep hA_top hA_bottom hb_top
      hdiag hupper hγ hΔA hΔb hG hg
/-- Compact Householder sequence route into the local least-squares QR
    backward-error specification.

    This is the implementation-nearest version of the supplied-sequence QR
    handoff: every panel and right-hand-side update is the compact rounded
    Householder dot/scale/subtract routine.  The theorem still keeps the final
    QR shape obligations explicit: the concrete loop must prove the final
    `[R;0]` transformed matrix, top transformed right-hand side, triangular
    shape of `R`, and the visible compact budget domination hypotheses. -/
theorem LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
    {m n r : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (R : Fin n → Fin n → ℝ) (cTop : Fin n → ℝ)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k, k < r →
      A_hat (k + 1) =
        fl_householderApplyCompactPanel fp m n (v k) (β k) (A_hat k))
    (hStepb : ∀ k, k < r →
      b_hat (k + 1) =
        fl_householderApplyCompact fp m (v k) (β k) (b_hat k))
    (horth : ∀ k, k < r →
      IsOrthogonal m (householder m (v k) (β k)))
    (hA_budget : ∀ k, k < r → ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k)
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k, k < r →
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k) (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_hat r i j = R ⟨i.val, hi⟩ j)
    (hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat r i j = 0)
    (hb_top : ∀ (i : Fin m) (hi : i.val < n),
      b_hat r i = cTop ⟨i.val, hi⟩)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ r - 1) * frobNormRect A +
            gamma fp n * frobNormRect (rectTopBlock (m := m) R))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ r - 1) * frobNormRect A +
            gamma fp n * frobNormRect (rectTopBlock (m := m) R))
          (((1 + cStep) ^ r - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R cTop) c_G c_g := by
  let η : ℝ := (1 + cStep) ^ r - 1
  have hη_nonneg : 0 ≤ η := by
    unfold η
    have hbase : (1 : ℝ) ≤ 1 + cStep := by linarith
    exact sub_nonneg.mpr (one_le_pow₀ hbase)
  rcases
    fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric
      fp m n r v β A b A_hat b_hat cStep hcStep hm
      hInitA hInitb hStepA hStepb horth hA_budget hb_budget with
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb⟩
  have hΔA : frobNormRect ΔA ≤ η * frobNormRect A := by
    apply frobNormRect_le_of_col_vecNorm2_le
    · exact hη_nonneg
    · intro j
      simpa [η] using hΔA_cols j
  exact
    LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget
      (m := m) (n := n) fp A ΔA b Δb (A_hat r) (b_hat r) Q R cTop
      (η * frobNormRect A) (η * vecNorm2 b) c_G c_g hQ hArep hbrep
      hA_top hA_bottom hb_top hdiag hupper hγ hΔA (by simpa [η] using hΔb)
      (by simpa [η] using hG) (by intro j; simpa [η] using hg j)
/-- Stored trailing Householder QR loop route into the local least-squares QR
    backward-error specification.

    This theorem is the concrete stored-loop handoff: the final top block
    `R` and transformed right-hand side `cTop` are read directly from the final
    stored outputs.  It reuses the Higham columnwise stored QR factorization
    assembly theorem, which supplies the common orthogonal factor, columnwise
    perturbation radii, `[R;0]`, `cTop`, and upper-triangularity in one package.
    The only triangular-solve algebraic condition kept visible is the
    nonzero diagonal/nonbreakdown hypothesis for the computed `R`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hdiag : ∀ i : Fin n,
      A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  let η : ℝ := (1 + cStep) ^ n - 1
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  let cTop : Fin n → ℝ :=
    fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
  rcases
    fl_householderStoredTrailingPanel_higham_columnwise_factorization
      fp hmn A b A_hat b_hat alpha cStep hcStep hm
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget with
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb,
      hA_top, hA_bottom, hb_top, hupper⟩
  have hη_nonneg : 0 ≤ η := by
    unfold η
    have hbase : (1 : ℝ) ≤ 1 + cStep := by linarith
    exact sub_nonneg.mpr (one_le_pow₀ hbase)
  have hΔA : frobNormRect ΔA ≤ η * frobNormRect A := by
    apply frobNormRect_le_of_col_vecNorm2_le
    · exact hη_nonneg
    · intro j
      simpa [η] using hΔA_cols j
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R cTop) c_G c_g
  exact
    LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget
      (m := m) (n := n) fp A ΔA b Δb (A_hat n) (b_hat n) Q R cTop
      (η * frobNormRect A) (η * vecNorm2 b) c_G c_g
      hQ hArep hbrep hA_top hA_bottom hb_top
      (by intro i; simpa [R] using hdiag i)
      (by simpa [R] using hupper)
      hγ hΔA (by simpa [η] using hΔb)
      (by simpa [η, R] using hG)
      (by intro j; simpa [η, R] using hg j)
/-- Stored trailing Householder QR solve certificate with a concrete
    floating-point nonbreakdown condition.

    This variant removes the unexplained final `Rᵢᵢ ≠ 0` hypothesis from
    `of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`.
    Instead, each pivot step assumes that the componentwise compact-update
    error budget at the diagonal entry is strictly smaller than the exact
    pivot magnitude `|alpha_k|`.  The QR module proves that this implies the
    final stored top block has nonzero diagonal. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  have hdiag : ∀ i : Fin n,
      A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 :=
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha
      fp hmn A_hat alpha hm hStepA halpha hden hbudgetDiag
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget
      hdiag hG hg
/-- Stored trailing Householder QR solve certificate with concrete pivot
    nonbreakdown and pivot-error conditions.

    This variant removes the denominator hypothesis `vᵀv ≠ 0` from the
    previous pivot-error theorem.  It is enough to assume at each step that the
    active stored pivot entry is not the selected `alpha_k`; the QR module
    proves that this implies the nonzero Householder denominator. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hpivotNe : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ alpha k)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  have hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
    intro k hk
    simpa using
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (hpivotNe k hk)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget
      hbudgetDiag hG hg
/-- Stored trailing Householder QR solve certificate using the standard
    Householder sign convention for denominator nonbreakdown.

    Compared with the pivot-value variant, this theorem replaces
    `A_hat[k,k] != alpha_k` by two source-style local conditions: the active
    trailing pivot column has positive squared norm and the selected `alpha_k`
    has nonpositive product with the active pivot entry.  The remaining
    nonbreakdown obligation is the visible floating-point budget inequality
    `budget_k < |alpha_k|`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  have hpivotNe : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ alpha k := by
    intro k hk
    simpa using
      householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (halpha k hk) (htrailingPos k hk) (hsign k hk)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hpivotNe hA_budget hb_budget
      hbudgetDiag hG hg
/-- Stored trailing Householder QR solve certificate with the standard signed
    Householder scalar made explicit.

    This closes the scalar sign-choice part of the solver-facing QR route.  The
    theorem assumes the source convention
    `alpha_k = signedHouseholderAlpha ||A_hat[k:m,k]||_2 A_hat[k,k]` and then
    derives both the squared-norm and sign hypotheses consumed by
    `..._of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`.  The
    remaining visible nonbreakdown assumptions are the positive trailing-column
    norm and the square-root compact-update budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k| := by
    intro k hk
    exact
      budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩)
        (halpha k hk) (hbudgetSqrt k hk)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha htrailingPos hsign
      hA_budget hb_budget hbudgetDiag hG hg
/-- Stored trailing Householder QR solve certificate from prefix-span
    nonbreakdown and a concrete active-entry budget.

    This solver-facing wrapper composes the prefix-span nonbreakdown bridge with
    the active-entry budget theorem.  It replaces the previous square-root
    budget hypothesis by the visible condition that, at each pivot, the compact
    diagonal update budget is smaller than the magnitude of some active trailing
    entry in the pivot column.  The theorem still does not derive that
    active-entry lower bound from rank or conditioning. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetEntry : ∀ k (hk : k < n),
      ∃ i : Fin m, k ≤ i.val ∧
        householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩ < |A_hat k i ⟨k, hk⟩|)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    exact
      householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan
        (A_hat k) (lt_of_lt_of_le hk hmn) hk
        (hnotspan k hk) (hprefixSpan k hk)
  have hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
    intro k hk
    simpa using
      householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (halpha k hk) (htrailingPos k hk) (hsign k hk)
  have hdiag : ∀ i : Fin n,
      A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 :=
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget
      fp hmn A_hat alpha hm hStepA halpha hnotspan hprefixSpan hsign
      hbudgetEntry
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget
      hdiag hG hg
/-- Stored trailing Householder QR solve certificate from prefix-span
    nonbreakdown and a dimensioned trailing-norm budget.

    This solver-facing wrapper uses the finite-dimensional norm-margin bridge:
    if `m * budget_k^2 < ||A_k(k:m,k)||_2^2`, then some active trailing entry
    has magnitude larger than the compact diagonal update budget.  The
    resulting active-entry witness feeds the prefix-span solver certificate. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have hbudgetEntry : ∀ k (hk : k < n),
      ∃ i : Fin m, k ≤ i.val ∧
        householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩ < |A_hat k i ⟨k, hk⟩| := by
    intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget_nonneg : 0 ≤ budget := by
      simpa [budget, beta, v, p] using
        householderCompactComponentBudget_nonneg fp m v beta
          (fun a => A_hat k a ⟨k, hk⟩) hm p
    have hmargin :
        (m : ℝ) * budget ^ 2 <
          householderTrailingNorm2Sq m p
            (fun a => A_hat k a ⟨k, hk⟩) := by
      simpa [budget, beta, v, p] using hbudgetNormSq k hk
    simpa [budget, beta, v, p] using
      exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq
        m p (fun a => A_hat k a ⟨k, hk⟩) budget
        hbudget_nonneg hmargin
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hnotspan hprefixSpan hsign
      hA_budget hb_budget hbudgetEntry hG hg
/-- Stored trailing Householder QR solve certificate from prefix-span and a
    bounded leading-column dual.

    This solver-facing wrapper is the conditioning-oriented version of the
    norm-square budget theorem.  For each pivot, a leading-column dual row with
    squared norm at most `K k` and the displayed budget condition
    `m * budget_k^2 < 1 / K k` imply the required trailing-norm margin, then
    the existing norm-square-budget solver certificate applies. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hL : ∀ k (hk : k < n),
      qrLeadingColumnLeftInverse (A_hat k) hk (L k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hLnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun i : Fin m =>
        L k hk ⟨k, Nat.lt_succ_self k⟩ i) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk := by
    intro k hk
    exact qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse
      (A_hat k) hk (L k hk) (hL k hk)
  have hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget : (m : ℝ) * budget ^ 2 < 1 / K k := by
      simpa [budget, beta, v, p] using hbudgetDual k hk
    simpa [budget, beta, v, p] using
      dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget
        (A_hat k) (lt_of_lt_of_le hk hmn) hk (L k hk)
        (hL k hk) (hprefixSpan k hk) (K k) budget
        (hK k hk) (hLnorm k hk) hbudget
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hnotspan hprefixSpan hsign
      hA_budget hb_budget hbudgetNormSq hG hg
/-- Prefix-span QR least-squares certificate with repository Gram/RHS radii.

    This is the source-faithful companion of the later prefix-local signed-alpha
    wrappers: it uses a leading-column dual witness and the prefix-span
    invariant to prove nonbreakdown, but chooses the final
    `qrSolveFinalGramBudget` and `qrSolveFinalRhsBudget` radii directly.
    Panel/RHS compact-update budget domination is still explicit here. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hL : ∀ k (hk : k < n),
      qrLeadingColumnLeftInverse (A_hat k) hk (L k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hLnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun i : Fin m =>
        L k hk ⟨k, Nat.lt_succ_self k⟩ i) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  have hcA :
      0 ≤ qrSolveFinalDataPerturbationBudget fp A R cStep :=
    qrSolveFinalDataPerturbationBudget_nonneg fp A R hcStep hγ
  have hcb :
      0 ≤ qrSolveFinalRhsPerturbationBudget (n := n) b cStep :=
    qrSolveFinalRhsPerturbationBudget_nonneg (n := n) b hcStep
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep)
  unfold qrSolveFinalGramBudget qrSolveFinalRhsBudget
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget
      fp hmn A b A_hat b_hat alpha L K cStep hcStep
      (frobNorm
        (rectLSGramPerturbationNormBudget A
          (qrSolveFinalDataPerturbationBudget fp A R cStep)))
      (∑ j : Fin n,
        rectLSRhsPerturbationNormBudget A b
          (qrSolveFinalDataPerturbationBudget fp A R cStep)
          (qrSolveFinalRhsPerturbationBudget (n := n) b cStep) j)
      hm hγ hInitA hInitb hStepA hStepb halpha hL hprefixSpan hK
      hLnorm hsign hA_budget hb_budget hbudgetDual
      (by
        simp [R, qrSolveFinalDataPerturbationBudget])
      (by
        intro j
        exact rectLSRhsPerturbationNormBudget_le_sum A b hcA hcb j)
/-- Prefix-span QR least-squares certificate with repository compact-update
    and final solver budgets.

    This removes the separate panel/RHS compact-update domination hypotheses
    from the source-faithful leading-dual route by choosing
    `storedQRCompactSequenceRelativeBudget`.  The remaining visible
    assumptions are the leading-column dual witness, the prefix-span invariant,
    the dual norm budget, and the compact smallness condition. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hL : ∀ k (hk : k < n),
      qrLeadingColumnLeftInverse (A_hat k) hk (L k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hLnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun i : Fin m =>
        L k hk ⟨k, Nat.lt_succ_self k⟩ i) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget
      fp hmn A b A_hat b_hat alpha L K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hL hprefixSpan hK hLnorm hsign
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
/-- Stored trailing Householder QR solve certificate from prefix-span and a
    local leading-block left inverse with a row-norm budget.

    The ambient leading-column dual used by the previous theorem is constructed
    by zero-padding the relevant row of the local leading-block left inverse. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  let L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ :=
    fun k hk p i =>
      if hi : i.val < k + 1 then C k hk p ⟨i.val, hi⟩ else 0
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget
      fp hmn A b A_hat b_hat alpha L K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha ?_ hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  · intro k hk
    exact
      qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
        hk (C k hk) (hC k hk)
  · intro k hk
    let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    calc
      vecNorm2Sq (fun i : Fin m => L k hk last i) =
          vecNorm2Sq (fun r : Fin (k + 1) => C k hk last r) := by
            simpa [L, last] using
              (qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
                (m := m) (k := k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
                (C k hk) last)
      _ ≤ K k := hCnorm k hk
/-- Local leading-block inverse row-budget QR certificate with repository
    Gram/RHS radii.

    This is the source-faithful left-inverse version of the explicit
    leading-dual wrapper: the ambient leading dual is zero-padded from a local
    left inverse of the current leading block, while the final Gram/RHS budgets
    are chosen to be the repository `qrSolveFinal*` expressions. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ :=
    fun k hk p i =>
      if hi : i.val < k + 1 then C k hk p ⟨i.val, hi⟩ else 0
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget
      fp hmn A b A_hat b_hat alpha L K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha ?_ hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual
  · intro k hk
    exact
      qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
        hk (C k hk) (hC k hk)
  · intro k hk
    let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    calc
      vecNorm2Sq (fun i : Fin m => L k hk last i) =
          vecNorm2Sq (fun r : Fin (k + 1) => C k hk last r) := by
            simpa [L, last] using
              (qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
                (m := m) (k := k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
                (C k hk) last)
      _ ≤ K k := hCnorm k hk
/-- Local leading-block inverse row-budget QR certificate with repository
    compact-update and final solver budgets.

    This removes the separate column/RHS compact-update domination hypotheses
    from the local left-inverse row-norm route by choosing
    `storedQRCompactSequenceRelativeBudget`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK hCnorm hsign
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
/-- Stored trailing Householder QR solve certificate from prefix-span and a
    local leading-block left inverse with a Frobenius-norm budget.

    This wrapper replaces the row-norm budget in the local-inverse theorem by
    the stronger but reusable inverse-norm condition
    `frobNorm (C k hk)^2 <= K k`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  exact (vecNorm2Sq_row_le_frobNorm_sq (C k hk) last).trans (hCfrob k hk)
/-- Local leading-block inverse Frobenius-budget QR certificate with
    repository Gram/RHS radii. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual
  intro k hk
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  exact (vecNorm2Sq_row_le_frobNorm_sq (C k hk) last).trans (hCfrob k hk)
/-- Local leading-block inverse Frobenius-budget QR certificate with
    repository compact-update and final solver budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK hCfrob hsign
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
/-- Stored trailing Householder QR solve certificate from prefix-span and a
    local leading-block left inverse with an infinity-norm budget.

    This solver-facing wrapper uses the shared `||C||_F^2 <= n ||C||_∞^2`
    bridge to feed the existing Frobenius-budget theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact (frobNorm_sq_le_nat_mul_infNorm_sq (C k hk)).trans (hCinf k hk)
/-- Local leading-block inverse infinity-budget QR certificate with repository
    Gram/RHS radii. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual
  intro k hk
  exact (frobNorm_sq_le_nat_mul_infNorm_sq (C k hk)).trans (hCinf k hk)
/-- Local leading-block inverse infinity-budget QR certificate with repository
    compact-update and final solver budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb halpha hC hprefixSpan hK hCinf hsign
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
/-- Local leading-block inverse row-budget QR certificate with the
    prefix-span invariant derived from the stored panel recurrence.

    This wrapper removes the separate `hprefixSpan` hypothesis from the
    source-faithful local-inverse route.  The stored Householder panel
    recurrence gives completed-column lower zeros, and local left inverses for
    the previous leading blocks convert those zeros into the prefix-span
    invariant used by the nonbreakdown argument. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha C K hm hγ
      hInitA hInitb hStepA hStepb halpha hC
      (fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose
        fp hmn A_hat alpha hStepA Cprev hCprev)
      hK hCnorm hsign hbudgetDual
/-- Local leading-block inverse Frobenius-budget QR certificate with the
    prefix-span invariant derived from the stored panel recurrence. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha C K hm hγ
      hInitA hInitb hStepA hStepb halpha hC
      (fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose
        fp hmn A_hat alpha hStepA Cprev hCprev)
      hK hCfrob hsign hbudgetDual
/-- Local leading-block inverse infinity-budget QR certificate with the
    prefix-span invariant derived from the stored panel recurrence. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha C K hm hγ
      hInitA hInitb hStepA hStepb halpha hC
      (fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose
        fp hmn A_hat alpha hStepA Cprev hCprev)
      hK hCinf hsign hbudgetDual
/-- Local leading-block inverse row-budget QR certificate with the stored
    prefix-span invariant and the source signed Householder alpha rule.

    This wrapper removes the separate squared-alpha and sign-choice hypotheses
    from the row-norm branch. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha Cprev C K hm hγ
      hInitA hInitb hStepA hStepb halpha hCprev hC hK hCnorm hsign hbudgetDual
/-- Local leading-block inverse Frobenius-budget QR certificate with the stored
    prefix-span invariant and the source signed Householder alpha rule. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha Cprev C K hm hγ
      hInitA hInitb hStepA hStepb halpha hCprev hC hK hCfrob hsign hbudgetDual
/-- Local leading-block inverse infinity-budget QR certificate with the stored
    prefix-span invariant and the source signed Householder alpha rule. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha Cprev C K hm hγ
      hInitA hInitb hStepA hStepb halpha hCprev hC hK hCinf hsign hbudgetDual
/-- Local leading-block determinant/row-budget QR certificate with the stored
    prefix-span invariant and the source signed Householder alpha rule.

    This wrapper removes the raw previous/current local left-inverse witnesses
    from the row-norm source-faithful route. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget
      fp hmn A b A_hat b_hat alpha
      (fun k hk =>
        nonsingInv k
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk))
      (fun k hk =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      K hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ ?_
      hK hCnorm hbudgetDual
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (hdetPrev k hk)).1
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hdetLead k hk)).1
/-- Local leading-block determinant/Frobenius-budget QR certificate with the
    stored prefix-span invariant and the source signed Householder alpha rule.

    This wrapper removes the raw previous/current local left-inverse witnesses
    from the Frobenius source-faithful route. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_frobNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n),
      frobNorm
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A b A_hat b_hat alpha
      (fun k hk =>
        nonsingInv k
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk))
      (fun k hk =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      K hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ ?_
      hK hCfrob hbudgetDual
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (hdetPrev k hk)).1
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hdetLead k hk)).1
/-- Local leading-block determinant/inverse-∞ QR certificate with the stored
    prefix-span invariant and the source signed Householder alpha rule.

    This wrapper removes the raw previous/current local left-inverse witnesses
    from the source-faithful stored-prefix route.  Callers expose nonsingularity
    of the previous transposed block and current leading block, plus the direct
    inverse-∞ budget for the repository `nonsingInv` of the current block. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          infNorm
            (nonsingInv (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha
      (fun k hk =>
        nonsingInv k
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk))
      (fun k hk =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      K hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ ?_
      hK hCinf hbudgetDual
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (hdetPrev k hk)).1
  · intro k hk
    exact
      (isInverse_nonsingInv_of_det_ne_zero (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hdetLead k hk)).1
/-- Source-faithful signed-alpha determinant QR certificate from local
    \(\kappa_\infty\) self-norm budgets.

    This wrapper removes the direct inverse-∞ budget from the preceding
    determinant route.  It derives
    `(k+1) * ‖nonsingInv(S_k)‖∞^2 <= K_k` from nonzero determinant,
    a local `κ∞` bound, and the displayed self-norm squared budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget
      fp hmn A b A_hat b_hat alpha K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetPrev hdetLead hK ?_ hbudgetDual
  intro k hk
  exact
    infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero
      (k + 1) (Nat.succ_pos k)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      (nonsingInv (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      (κ k) (K k) (hdetLead k hk) (hκ k hk) (hκbudget k hk)
/-- Source-faithful signed-alpha QR certificate from triangular leading blocks
    and local \(\kappa_\infty\) self-norm budgets.

    This wrapper derives the previous/current determinant hypotheses in the
    preceding route from a visible upper-triangular leading shape and nonzero
    leading diagonal entries.  It remains a visible-domain theorem: it does not
    derive the triangular/nonzero-diagonal invariant from full column rank. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hupper : ∀ k (_hk : k < n) (i : Fin m) (j : Fin n),
      j.val < i.val → A_hat k i j = 0)
    (hdiag : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
          (qrLeadingRow m k
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
          (qrLeadingColumn n k hk r) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef ?_ ?_ hK hκ hκbudget hbudgetDual
  · intro k hk
    let hkm : k ≤ m := le_trans (Nat.le_of_lt hk) hmn
    let hkm1 : k + 1 ≤ m :=
      Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
    exact
      qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) hkm hk (hupper k hk) (fun r => by
          let r' : Fin (k + 1) :=
            ⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self k)⟩
          simpa [qrLeadingRow, qrPrefixRow, qrLeadingColumn, qrPreviousColumn,
            hkm, hkm1, r'] using hdiag k hk r')
  · intro k hk
    exact
      qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
        (hupper k hk) (hdiag k hk)
/-- Stored trailing Householder QR solve certificate from nonsingular local
    leading blocks and a visible inverse ∞-norm budget.

    This determinant-facing wrapper removes the explicit local left-inverse
    witness from the inverse-∞ route by using `nonsingInv` for each leading
    block.  The quantitative inverse-norm budget remains a visible domain
    assumption, so this is not an SVD, condition-number, or determinant-margin
    estimate. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          infNorm
            (nonsingInv (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha
      (fun k hk =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha ?_ hprefixSpan hK hCinf
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact
    (isInverse_nonsingInv_of_det_ne_zero (k + 1)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      (hdetLead k hk)).1
/-- Stored trailing Householder QR solve certificate from nonsingular local
    leading blocks and a local \(\kappa_\infty\) budget.

    This condition-number-facing wrapper derives the inverse-∞ budget required
    by the previous determinant-facing route from a positive lower bound
    `ρ_k ≤ ‖S_k‖∞`, a bound `κ∞(S_k) ≤ κ_k`, and the displayed squared
    budget `(k+1)(κ_k/ρ_k)^2 ≤ K_k`.  It still keeps the condition-number and
    lower-norm bounds visible; it does not derive them from SVD or a
    computed-loop invariant. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ ρ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hρ : ∀ k (_hk : k < n), 0 < ρ k)
    (hρ_le : ∀ k (hk : k < n),
      ρ k ≤
        infNorm
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (_hk : k < n),
      ((k + 1 : ℕ) : ℝ) * (κ k / ρ k) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget
      fp hmn A b A_hat b_hat alpha K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetLead hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact
    infNorm_sq_budget_of_kappaInf_le_and_norm_lower
      (k + 1) (Nat.succ_pos k)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      (nonsingInv (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      (κ k) (ρ k) (K k) (hρ k hk) (hρ_le k hk)
      (hκ k hk) (hκbudget k hk)
/-- Stored trailing Householder QR solve certificate from local determinant and
    \(\kappa_\infty\) budgets, without a separate lower-norm parameter.

    This specializes the previous condition-number route with
    `rho_k = ‖S_k‖∞`.  The determinant hypothesis supplies
    `0 < ‖S_k‖∞`, so the visible budget is stated directly with the local
    leading-block infinity norm. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget
      fp hmn A b A_hat b_hat alpha K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetLead hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact
    infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero
      (k + 1) (Nat.succ_pos k)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      (nonsingInv (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      (κ k) (K k) (hdetLead k hk) (hκ k hk) (hκbudget k hk)
/-- Stored trailing Householder QR solve certificate from local determinant and
    \(\kappa_\infty\) budgets, deriving prefix span from the previous leading
    block.

    Compared with the preceding self-norm condition-number route, this wrapper
    no longer assumes the abstract `qrPrefixSupportSpannedByPreviousColumns`
    invariant.  It derives that invariant from the nonzero determinant of the
    previous transposed leading block and the QR lower-zero shape of the
    completed columns.  Local determinant and condition-number bounds for the
    current leading blocks, sign choice, compact-update budgets, and final
    solver budgets remain visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetLead ?_
      hK hκ hκbudget hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact
    qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose
      (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
      (hdetPrev k hk) (hlowerPrev k hk)
/-- Stored trailing Householder QR solve certificate from triangular local
    leading blocks and self-norm \(\kappa_\infty\) budgets.

    This is the triangular-principal-minor version of
    `..._of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`: the previous
    and current determinant hypotheses, and the completed-column lower-zero
    shape needed for prefix span, are derived from the visible upper-triangular
    shape and nonzero local diagonal hypotheses.  It remains a visible-domain
    theorem; it does not prove that a generic full-rank input or a computed QR
    loop supplies these triangular/nonzero-diagonal hypotheses. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hupper : ∀ k (_hk : k < n) (i : Fin m) (j : Fin n),
      j.val < i.val → A_hat k i j = 0)
    (hdiagPrev : ∀ k (hk : k < n) (r : Fin k),
      A_hat k
        (qrPrefixRow m k (le_trans (Nat.le_of_lt hk) hmn) r)
        (qrPreviousColumn n k hk r) ≠ 0)
    (hdiagLead : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
        (qrLeadingRow m k
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
        (qrLeadingColumn n k hk r) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
    intro k hk
    exact
      qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
        (hupper k hk) (hdiagPrev k hk)
  have hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    exact
      qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
        (hupper k hk) (hdiagLead k hk)
  have hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 := by
    intro k hk i j hki
    exact hupper k hk i (qrPreviousColumn n k hk j)
      (Nat.lt_of_lt_of_le j.isLt hki)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetPrev hdetLead hlowerPrev
      hK hκ hκbudget hsign hA_budget hb_budget hbudgetDual hG hg
/-- Stored trailing Householder QR solve certificate from computed prefix
    lower-zero shape, triangular local diagonal nonzeros, and self-norm
    \(\kappa_\infty\) budgets.

    This removes the broad triangular-shape hypothesis from
    `..._of_triangular_leading_blocks_kappaInf_selfNorm_budget`.  The stored
    panel recurrence itself supplies the only triangular entries needed by the
    previous/current leading-block determinant bridges and by the prefix-span
    lower-zero bridge.  The remaining visible assumptions are the nonzero local
    diagonals, local condition-number budgets, sign choice, compact-update
    budgets, and final Gram/RHS budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdiagPrev : ∀ k (hk : k < n) (r : Fin k),
      A_hat k
        (qrPrefixRow m k (le_trans (Nat.le_of_lt hk) hmn) r)
        (qrPreviousColumn n k hk r) ≠ 0)
    (hdiagLead : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
        (qrLeadingRow m k
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
        (qrLeadingColumn n k hk r) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  let vStep : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else
      0
  let βStep : ℕ → ℝ := fun k =>
    if hk : k < n then
      householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
    else
      0
  have hStepA_shape : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (vStep k) (βStep k) (A_hat k) := by
    intro k hk
    simpa [vStep, βStep, hk] using hStepA k hk
  have hprefixLower :
      ∀ k, k ≤ n →
        ∀ (i : Fin m) (j : Fin n),
          j.val < k → j.val < i.val → A_hat k i j = 0 :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      (m := m) (n := n) fp vStep βStep A_hat hStepA_shape
  have hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
    intro k hk
    apply
      qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
        (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
    · intro i j hij
      simpa [qrPreviousLeadingBlockTranspose] using
        hprefixLower k (Nat.le_of_lt hk)
          (qrPrefixRow m k (le_trans (Nat.le_of_lt hk) hmn) j)
          (qrPreviousColumn n k hk i) i.isLt
          (by simpa [qrPrefixRow, qrPreviousColumn] using hij)
    · exact hdiagPrev k hk
  have hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    apply
      qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
    · intro i j hji
      have hjk : j.val < k := Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ i.isLt)
      simpa [qrLeadingBlock] using
        hprefixLower k (Nat.le_of_lt hk)
          (qrLeadingRow m k
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)
          (by simpa [qrLeadingColumn] using hjk)
          (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
    · exact hdiagLead k hk
  have hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 := by
    intro k hk i j hki
    simpa [qrPreviousColumn] using
      hprefixLower k (Nat.le_of_lt hk) i
        (qrPreviousColumn n k hk j) j.isLt
        (Nat.lt_of_lt_of_le j.isLt hki)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetPrev hdetLead hlowerPrev
      hK hκ hκbudget hsign hA_budget hb_budget hbudgetDual hG hg
/-- Computed prefix-zero triangular self-norm QR certificate with the standard
    signed Householder scalar made explicit.

    This is the sign-choice specialization of
    `..._of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`.
    The theorem replaces the independent squared-norm and sign hypotheses by
    the concrete source convention that each `alpha_k` is the signed trailing
    norm of the current pivot column.  It still exposes the remaining red
    bottleneck dependencies: local diagonal nonzeros, local `κ∞` budgets,
    compact-update budgets, and final Gram/RHS solver budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdiagPrev : ∀ k (hk : k < n) (r : Fin k),
      A_hat k
        (qrPrefixRow m k (le_trans (Nat.le_of_lt hk) hmn) r)
        (qrPreviousColumn n k hk r) ≠ 0)
    (hdiagLead : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
        (qrLeadingRow m k
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
        (qrLeadingColumn n k hk r) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdiagPrev hdiagLead
      hK hκ hκbudget hsign hA_budget hb_budget hbudgetDual hG hg
/-- Computed prefix-zero triangular self-norm QR certificate with previous
    diagonal nonzeros generated by the stored loop.

    This narrows the nonzero-diagonal part of the red QR bottleneck.  The
    earlier pivots in each local leading block are proved from the stored
    sequence plus the signed-alpha nonbreakdown budget; the theorem keeps only
    the current local pivot nonzero condition visible.  It does not prove that
    ordinary full column rank forces these current leading principal pivots to
    be nonzero. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget_nonneg : 0 ≤ budget := by
      simpa [budget, beta, v, p] using
        householderCompactComponentBudget_nonneg fp m v beta
          (fun a => A_hat k a ⟨k, hk⟩) hm p
    simpa [budget, beta, v, p] using
      householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt
        m p (fun a => A_hat k a ⟨k, hk⟩) budget
        hbudget_nonneg (hbudgetSqrt k hk)
  have hdiagPrefix :
      ∀ k (hk : k ≤ n) (i : Fin k),
        A_hat k
          ⟨i.val, lt_of_lt_of_le i.isLt (le_trans hk hmn)⟩
          ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ ≠ 0 :=
    fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget
      fp hmn A_hat alpha hm hStepA hAlphaDef htrailingPos hbudgetSqrt
  have hdiagPrev : ∀ k (hk : k < n) (r : Fin k),
      A_hat k
        (qrPrefixRow m k (le_trans (Nat.le_of_lt hk) hmn) r)
        (qrPreviousColumn n k hk r) ≠ 0 := by
    intro k hk r
    simpa [qrPrefixRow, qrPreviousColumn] using
      hdiagPrefix k (Nat.le_of_lt hk) r
  have hdiagLead : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
        (qrLeadingRow m k
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
        (qrLeadingColumn n k hk r) ≠ 0 := by
    intro k hk r
    by_cases hr : r.val < k
    · let rp : Fin k := ⟨r.val, hr⟩
      have hp := hdiagPrefix k (Nat.le_of_lt hk) rp
      simpa [qrLeadingRow, qrLeadingColumn, qrPrefixRow, qrPreviousColumn, rp] using hp
    · have hr_eq : r.val = k := by omega
      simpa [qrLeadingRow, qrLeadingColumn, hr_eq] using hdiagPivot k hk
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb hAlphaDef hdiagPrev hdiagLead
      hK hκ hκbudget hA_budget hb_budget hbudgetDual hG hg
/-- Explicit-budget version of the prefix-local signed-alpha stored QR
    certificate.

    This removes the final Gram/RHS domination hypotheses by choosing the
    repository's induced QR least-squares radii themselves:
    `qrSolveFinalGramBudget` and `qrSolveFinalRhsBudget`.  The remaining visible
    assumptions are the current-pivot nonzero condition, local `κ∞` budgets,
    compact-update budgets, and the per-pivot square-root budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  have hcA :
      0 ≤ qrSolveFinalDataPerturbationBudget fp A R cStep :=
    qrSolveFinalDataPerturbationBudget_nonneg fp A R hcStep hγ
  have hcb :
      0 ≤ qrSolveFinalRhsPerturbationBudget (n := n) b cStep :=
    qrSolveFinalRhsPerturbationBudget_nonneg (n := n) b hcStep
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep)
  unfold qrSolveFinalGramBudget qrSolveFinalRhsBudget
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep
      (frobNorm
        (rectLSGramPerturbationNormBudget A
          (qrSolveFinalDataPerturbationBudget fp A R cStep)))
      (∑ j : Fin n,
        rectLSRhsPerturbationNormBudget A b
          (qrSolveFinalDataPerturbationBudget fp A R cStep)
          (qrSolveFinalRhsPerturbationBudget (n := n) b cStep) j)
      hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      hbudgetSqrt hdiagPivot hK hκ hκbudget hA_budget hb_budget
      hbudgetDual
      (by
        simp [R, qrSolveFinalDataPerturbationBudget])
      (by
        intro j
        exact rectLSRhsPerturbationNormBudget_le_sum A b hcA hcb j)
/-- Prefix-local signed-alpha QR least-squares certificate with repository
    radii for both the compact-update constant and the final Gram/RHS budgets.

    This removes the separate compact panel/RHS budget-domination hypotheses by
    choosing the deterministic sequence budget
    `storedQRCompactSequenceRelativeBudget`.  The remaining visible assumptions
    are the current-pivot nonzero condition, local `κ∞` budgets, and the
    per-pivot square-root/diagonal budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget_nonneg : 0 ≤ budget := by
      simpa [budget, beta, v, p] using
        householderCompactComponentBudget_nonneg fp m v beta
          (fun a => A_hat k a ⟨k, hk⟩) hm p
    simpa [budget, beta, v, p] using
      householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt
        m p (fun a => A_hat k a ⟨k, hk⟩) budget
        hbudget_nonneg (hbudgetSqrt k hk)
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K cStep hcStep hm hγ
      hInitA hInitb hStepA hStepb hAlphaDef hbudgetSqrt
      hdiagPivot hK hκ hκbudget
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
/-- Explicit compact-budget QR least-squares certificate with the pivot budget
    stated as a dimensioned trailing-norm-square margin.

    This is the solver-facing version of the direct norm-square-to-square-root
    bridge: the theorem replaces the visible hypothesis
    `budget_k < sqrt (||A_k(k:m,k)||_2^2)` by the conditioning-friendly margin
    `m * budget_k^2 < ||A_k(k:m,k)||_2^2`, then derives the square-root budget
    internally before applying the latest explicit compact-budget certificate.
    The theorem still leaves the current-pivot nonzero condition, local
    `κ∞` assumptions, and the dual/conditioning budget visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)) := by
    intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget_nonneg : 0 ≤ budget := by
      simpa [budget, beta, v, p] using
        householderCompactComponentBudget_nonneg fp m v beta
          (fun a => A_hat k a ⟨k, hk⟩) hm p
    have hmargin :
        (m : ℝ) * budget ^ 2 <
          householderTrailingNorm2Sq m p
            (fun a => A_hat k a ⟨k, hk⟩) := by
      simpa [budget, beta, v, p] using hbudgetNormSq k hk
    simpa [budget, beta, v, p] using
      budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq
        m p (fun a => A_hat k a ⟨k, hk⟩) budget
        hbudget_nonneg hmargin
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget
      fp hmn A b A_hat b_hat alpha κ K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hbudgetSqrt hdiagPivot hK hκ hκbudget hbudgetDual
/-- Explicit compact-budget QR least-squares certificate with norm-square pivot
    margins, deriving the current-pivot nonzero condition from nonsingular
    stored leading blocks and the stored lower-zero shape.

    This is a structured no-pivot route.  It does not claim that ordinary full
    column rank is enough; instead, each displayed leading principal block must
    be nonsingular.  The stored-loop lower-zero theorem then turns that local
    determinant hypothesis into the current pivot nonzero condition consumed by
    triangular back substitution. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0 :=
    fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero
      fp hmn A_hat alpha hStepA hdetLead
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget
      fp hmn A b A_hat b_hat alpha κ K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hbudgetNormSq hdiagPivot hK hκ hκbudget hbudgetDual
/-- Explicit compact-budget QR least-squares certificate from structured
    nonsingular leading blocks and local `κ∞`/dual budgets.

    Compared with
    `..._leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`, this theorem
    removes the separate trailing-norm-square pivot-margin hypothesis.  The
    stored lower-zero shape makes the displayed local leading block
    upper-triangular, its nonzero determinant gives the prefix-span and current
    pivot facts, the existing `κ∞` bridge bounds the local inverse infinity
    norm, and the displayed dual budget then supplies the dimensioned
    norm-square margin. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k => householderBetaSpec m (v k)
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hprefix :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep
  have hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    let hkm : k + 1 ≤ m :=
      Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
    let S : Fin (k + 1) → Fin (k + 1) → ℝ :=
      qrLeadingBlock (A_hat k) hkm hk
    let C : Fin (k + 1) → Fin (k + 1) → ℝ :=
      nonsingInv (k + 1) S
    let budget : ℝ :=
      householderCompactComponentBudget fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (fun a => A_hat k a ⟨k, hk⟩)
        ⟨k, lt_of_lt_of_le hk hmn⟩
    have hupper : ∀ i j : Fin (k + 1), j.val < i.val →
        qrLeadingBlock (A_hat k) hkm hk i j = 0 := by
      intro i j hji
      have hjk : j.val < k := by omega
      exact
        hprefix k (Nat.le_of_lt hk)
          (qrLeadingRow m k hkm i)
          (qrLeadingColumn n k hk j)
          (by simpa [qrLeadingColumn] using hjk)
          (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
    have hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
        A_hat k i (qrPreviousColumn n k hk j) = 0 := by
      intro i j hi
      exact
        hprefix k (Nat.le_of_lt hk) i (qrPreviousColumn n k hk j)
          (by simp [qrPreviousColumn])
          (lt_of_lt_of_le j.isLt hi)
    have hprefixSpan : qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk :=
      qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero
        (A_hat k) hkm hk hupper (by simpa [hkm] using hdetLead k hk)
        hlowerPrev
    have hC : IsLeftInverse (k + 1) S C := by
      exact
        (isInverse_nonsingInv_of_det_ne_zero (k + 1) S
          (by simpa [S, hkm] using hdetLead k hk)).1
    have hCinf : ((k + 1 : ℕ) : ℝ) * infNorm C ^ 2 ≤ K k := by
      simpa [S, C, hkm] using
        infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero
          (k + 1) (Nat.succ_pos k) S C (κ k) (K k)
          (by simpa [S, hkm] using hdetLead k hk)
          (by simpa [S, C, hkm] using hκ k hk)
          (by simpa [S, hkm] using hκbudget k hk)
    simpa [budget, S, C, hkm] using
      dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_infNorm_budget
        (A_hat k) hkm hk C hC hprefixSpan (K k) budget
        (hK k hk) hCinf (by simpa [budget] using hbudgetDual k hk)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget
      fp hmn A b A_hat b_hat alpha κ K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hbudgetNormSq hdetLead hK hκ hκbudget hbudgetDual
/-- Explicit compact-budget QR least-squares certificate from structured
    nonsingular leading blocks and direct inverse-∞/dual budgets.

    This is the same structured local-leading-block route as
    `..._leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`, but it
    removes the local `κ∞` and self-norm budget hypotheses.  Instead, callers
    provide the direct inverse-∞ budget
    `(k+1) * ‖nonsingInv(S_k)‖∞^2 ≤ K_k`.  The proof reuses the existing
    repository theorem
    `..._leadingBlock_det_ne_zero_infNorm_budget`, while deriving prefix-span
    from the stored lower-zero shape and instantiating both compact-update and
    final Gram/RHS budgets with the repository radii. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          infNorm
            (nonsingInv (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hcStep : 0 ≤ cStep := by
    simpa [cStep] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  let R : Fin n → Fin n → ℝ :=
    fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
  have hcA :
      0 ≤ qrSolveFinalDataPerturbationBudget fp A R cStep :=
    qrSolveFinalDataPerturbationBudget_nonneg fp A R hcStep hγ
  have hcb :
      0 ≤ qrSolveFinalRhsPerturbationBudget (n := n) b cStep :=
    qrSolveFinalRhsPerturbationBudget_nonneg (n := n) b hcStep
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k => householderBetaSpec m (v k)
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hprefixLower :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep
  have hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk := by
    intro k hk
    let hkm : k + 1 ≤ m :=
      Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
    have hupper : ∀ i j : Fin (k + 1), j.val < i.val →
        qrLeadingBlock (A_hat k) hkm hk i j = 0 := by
      intro i j hji
      have hjk : j.val < k := by omega
      exact
        hprefixLower k (Nat.le_of_lt hk)
          (qrLeadingRow m k hkm i)
          (qrLeadingColumn n k hk j)
          (by simpa [qrLeadingColumn] using hjk)
          (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
    have hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
        A_hat k i (qrPreviousColumn n k hk j) = 0 := by
      intro i j hi
      exact
        hprefixLower k (Nat.le_of_lt hk) i (qrPreviousColumn n k hk j)
          (by simp [qrPreviousColumn])
          (lt_of_lt_of_le j.isLt hi)
    exact
      qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero
        (A_hat k) hkm hk hupper (by simpa [hkm] using hdetLead k hk)
        hlowerPrev
  change
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep)
  unfold qrSolveFinalGramBudget qrSolveFinalRhsBudget
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget
      fp hmn A b A_hat b_hat alpha K cStep hcStep
      (frobNorm
        (rectLSGramPerturbationNormBudget A
          (qrSolveFinalDataPerturbationBudget fp A R cStep)))
      (∑ j : Fin n,
        rectLSRhsPerturbationNormBudget A b
          (qrSolveFinalDataPerturbationBudget fp A R cStep)
          (qrSolveFinalRhsPerturbationBudget (n := n) b cStep) j)
      hm hγ hInitA hInitb hStepA hStepb halpha hdetLead hprefixSpan hK
      hCinf hsign
      (fun k hk j => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_column_bound
            hmn fp A_hat b_hat alpha hm k hk j)
      (fun k hk => by
        simpa [cStep] using
          storedQRCompactSequenceRelativeBudget_rhs_bound
            hmn fp A_hat b_hat alpha hm k hk)
      hbudgetDual
      (by
        simp [R, qrSolveFinalDataPerturbationBudget])
      (by
        intro j
        exact rectLSRhsPerturbationNormBudget_le_sum A b hcA hcb j)
/-- Explicit compact-budget QR least-squares certificate from diagonally
    dominant nonsingular leading blocks.

    This is the determinant-facing diagonal-dominance version of
    `..._leadingBlock_det_ne_zero_invNorm_dualBudget`.  It uses Higham's
    triangular inverse bound already formalized in `InverseBounds.lean` to
    derive the direct inverse-∞ budget for each local leading block.  The dual
    compact-budget inequality remains visible because it is the quantitative
    condition that converts inverse control into a pivot-margin bound. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hKbound : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (2 ^ k *
            (1 / Finset.inf' Finset.univ
              ⟨(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)), Finset.mem_univ _⟩
              (fun r : Fin (k + 1) =>
                |qrLeadingBlock (A_hat k)
                    (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk r r|))) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget
      fp hmn A b A_hat b_hat alpha K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hK ?_ hbudgetDual
  intro k hk
  exact
    triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero (k + 1)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      ⟨k, Nat.lt_succ_self k⟩
      (K k)
      (hDD k hk)
      (by simpa using hdetLead k hk)
      (by simpa using hKbound k hk)
/-- Diagonal-dominant structured QR certificate with the auxiliary inverse
    budget chosen concretely.

    This removes the arbitrary `K_k` parameter from the preceding theorem.
    For each pivot, let `D_k` be the explicit Higham diagonal-dominant inverse
    budget
    `(k+1) * (2^k / min_r |S_k(r,r)|)^2`.  Choosing `K_k = 2 D_k`
    automatically supplies the inverse-budget side condition.  The remaining
    quantitative pivot-margin condition is the direct smallness hypothesis
    `m * B_k^2 < 1 / (2 D_k)` for the compact Householder component budget
    `B_k`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hbudgetConcrete : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 /
          (2 *
            diagDominantUpperInvBudgetExpr (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
              ⟨k, Nat.lt_succ_self k⟩)) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  let K : ℕ → ℝ := fun k =>
    if hk : k < n then
      2 *
        diagDominantUpperInvBudgetExpr (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          ⟨k, Nat.lt_succ_self k⟩
    else 1
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget
      fp hmn A b A_hat b_hat alpha K hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hDD ?_ ?_ ?_
  · intro k hk
    have hDpos :
        0 <
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ :=
      diagDominantUpperInvBudgetExpr_pos (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        ⟨k, Nat.lt_succ_self k⟩
        (hDD k hk)
    simp [K, hk, hDpos]
  · intro k hk
    have hDnonneg :
        0 ≤
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ :=
      le_of_lt
        (diagDominantUpperInvBudgetExpr_pos (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          ⟨k, Nat.lt_succ_self k⟩
          (hDD k hk))
    have hle :
        diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ ≤
          2 *
            diagDominantUpperInvBudgetExpr (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
              ⟨k, Nat.lt_succ_self k⟩ := by
      linarith
    simpa [K, hk, diagDominantUpperInvBudgetExpr] using hle
  · intro k hk
    simpa [K, hk] using hbudgetConcrete k hk
/-- Product-form companion to the concrete dual-budget route.

    This theorem replaces the direct denominator hypothesis
    `m * B_k^2 < 1 / (2D_k)` by the equivalent sufficient product-form
    smallness condition `2D_k * (m * B_k^2) < 1`.  The local scalar bridge is
    useful in downstream audits because all denominator positivity is derived
    from diagonal dominance through `diagDominantUpperInvBudgetExpr_pos`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hbudgetProduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hDD ?_
  intro k hk
  exact
    mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one
      (diagDominantUpperInvBudgetExpr_pos (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        ⟨k, Nat.lt_succ_self k⟩
        (hDD k hk))
      (hbudgetProduct k hk)
/-- Product-form concrete-dual route using the deterministic stored QR
    sequence budget.

    Compared with
    `..._concreteDualProductBudget`, this wrapper does not ask for product
    smallness of the raw pivot compact component directly.  Instead it uses the
    repository's stored-loop compact sequence budget and the current
    pivot-column norm; the local scalar bridge
    `storedQRCompactPivotBudget_le_sequence_column_norm` then supplies the
    componentwise product condition consumed by the previous theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hbudgetSequenceProduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hDD ?_
  intro k hk
  let D :=
    diagDominantUpperInvBudgetExpr (k + 1)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      ⟨k, Nat.lt_succ_self k⟩
  let budget :=
    householderCompactComponentBudget fp m
      (householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
      (householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
      (fun a => A_hat k a ⟨k, hk⟩)
      ⟨k, lt_of_lt_of_le hk hmn⟩
  let B :=
    storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
      vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)
  have hD_nonneg : 0 ≤ D := by
    exact le_of_lt
      (diagDominantUpperInvBudgetExpr_pos (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        ⟨k, Nat.lt_succ_self k⟩
        (hDD k hk))
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbudget_nonneg : 0 ≤ budget := by
    simpa [budget] using
      householderCompactComponentBudget_nonneg fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (fun a => A_hat k a ⟨k, hk⟩) hm
        ⟨k, lt_of_lt_of_le hk hmn⟩
  have hbudget_le : budget ≤ B := by
    simpa [budget, B] using
      storedQRCompactPivotBudget_le_sequence_column_norm
        hmn fp A_hat b_hat alpha hm k hk
  exact
    two_mul_mul_sq_lt_one_of_nonneg_le
      hD_nonneg hm_nonneg hbudget_nonneg hbudget_le
      (by simpa [D, B] using hbudgetSequenceProduct k hk)
/-- Solver-facing equation (8) QR certificate from the explicit
    off-diagonal-control invariant.

    This is the first positive route after the red-bottleneck choice: instead
    of pretending that diagonal dominance or compact-product smallness follows
    from the ordinary unpivoted Householder recurrence, the theorem exposes a
    single stronger computed-loop invariant and proves that it supplies the
    previously listed diagonal-dominant/product-sequence assumptions. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff :
      StoredQROffDiagonalControlInvariant hmn fp A_hat b_hat alpha) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      hoff.leadingBlock_det_ne_zero
      hoff.leadingBlock_diagDominant
      hoff.compact_sequence_product_small
/-- Solver-facing QR certificate from the source-shaped off-diagonal-control
    data.  This is a stricter but more primitive route than
    `StoredQROffDiagonalControlInvariant`: local triangular shape, nonzero
    diagonals, row off-diagonal domination, and stored-sequence product
    smallness imply the packaged invariant, which then feeds the existing
    solver theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff :
      StoredQRSourceOffDiagonalControl hmn fp A_hat b_hat alpha) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl
        hmn fp A_hat b_hat alpha hoff)
/-- Solver-facing stored-QR certificate from diagonal-dominant local leading
    blocks, local `κ∞`/dual-budget nonbreakdown, and a finite global
    compact-product budget.

    This is the implementation-facing version of the diagonal-dominance
    source-control route.  It closes the off-diagonal/diagonal-lower-bound
    field by assuming the repository's local `IsDiagDominantUpper` statement
    for each displayed leading block, then reuses the existing
    source-control solver theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct
        hmn fp A_hat b_hat alpha κ K hm hStepA hAlphaDef hdetLead hDD
        hK hκ hκbudget hbudgetDual hglobalProduct)
/-- Solver-facing stored-QR certificate from diagonal-dominant local leading
    blocks and the canonical finite-max product-smallness scalar condition.

    This is the main route-1 theorem surface after the finite-max closure: the
    raw `storedQRCompactSequenceProductBudget < 1` field is replaced by the
    single scalar inequality over the canonical maxima
    `storedQRDiagDominantInvFactorBudget` and
    `storedQRPivotColumnNormBudget`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
        hmn fp A_hat b_hat alpha κ K hm hStepA hAlphaDef hdetLead hDD
        hK hκ hκbudget hbudgetDual hsmall)
/-- Solver-facing stored-QR certificate from diagonal-dominant local leading
    blocks and the canonical finite-max product-smallness scalar condition,
    using the concrete diagonal-dominant dual-budget route.

    Compared with the `κ∞`/dual-budget finite-max theorem above, this wrapper
    does not expose auxiliary `κ`/`K` sequences or a separate dual compact-budget
    field.  The existing concrete diagonal-dominant theorem supplies the local
    inverse budget from `diagDominantUpperInvBudgetExpr`, and the finite-max
    scalar condition implies each per-pivot product inequality consumed by that
    theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hproduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1 :=
    storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness
      hmn fp A_hat b_hat alpha hm (fun k => hDD k.val k.isLt) hsmall
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hDD ?_
  intro k hk
  exact
    lt_of_le_of_lt
      (storedQRCompactSequenceProductExpr_le_budget hmn fp A_hat b_hat alpha
        (⟨k, hk⟩ : Fin n))
      hproduct
/-- Concrete-dual finite-max stored-QR certificate with determinant
    nonzeroness derived from `IsDiagDominantUpper`.

    Since `IsDiagDominantUpper` includes upper-triangular shape and nonzero
    diagonal entries, each displayed local leading block is nonsingular.  This
    wrapper therefore keeps only local diagonal dominance and the canonical
    finite-max smallness scalar as the visible QR-domain assumptions. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (fun k hk =>
        det_ne_zero_of_diagDominantUpper (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (hDD k hk))
      hDD hsmall
/-- Solver-facing stored-QR certificate from local diagonal dominance and the
    canonical finite-max rational-gamma source-denominator cap route.

    This is the equation (8) handoff for the newest source-denominator route:
    the solver certificate consumes the packaged off-diagonal-control invariant
    built from local diagonal dominance, source-shaped Householder denominator
    nonbreakdown, a displayed unit-roundoff cap, and the canonical scalar
    smallness inequality with
    `Gcap = (m * Ucap) / (1 - m * Ucap)`.  The theorem does not prove those
    source/domain hypotheses; it makes them the remaining visible obligations
    instead of reintroducing determinant, pointwise `Dcap`/`Ncap`, or separate
    rational-gamma domination fields. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds
        hmn fp A_hat b_hat alpha Ucap hm hDD
        hUcap_nonneg hden hu huCap hsmall)
/-- Solver-facing stored-QR certificate for the canonical rational-gamma route
    with source denominator nonbreakdown derived from signed-alpha data.

    This is the source-nonbreakdown reduction of
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`.
    The raw `v^T v != 0` hypothesis is replaced by positive active trailing
    norms; the signed-alpha definition supplies both the square-norm equation
    and the sign condition consumed by the scalar Householder nonbreakdown
    theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds
        hmn fp A_hat b_hat alpha Ucap hm hDD hUcap_nonneg
        halpha htrailingPos hsign hu huCap hsmall)
/-- Solver-facing stored-QR certificate for the canonical rational-gamma route
    with source denominator nonbreakdown derived from leading-block determinant
    data.

    This is the determinant/rank specialization of
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`.
    Nonzero determinants for the previous and current leading blocks, together
    with the previous-column lower-zero shape, supply the positive active
    trailing norms used by the signed-alpha nonbreakdown theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
        hmn fp A_hat b_hat alpha Ucap hm hDD hUcap_nonneg
        hAlphaDef hdetPrev hdetLead hlowerPrev hu huCap hsmall)
/-- Solver-facing stored-QR certificate for the canonical rational-gamma route
    with the current leading-block determinant derived from local diagonal
    dominance.

    The only determinant field left visible is the previous transposed
    leading-block determinant.  Current leading-block nonsingularity follows
    from the same `IsDiagDominantUpper` hypothesis used by the inverse-budget
    route. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds
        hmn fp A_hat b_hat alpha Ucap hm hDD hUcap_nonneg
        hAlphaDef hdetPrev hlowerPrev hu huCap hsmall)
/-- Solver-facing stored-QR certificate for the canonical rational-gamma route
    with both previous and current local determinant fields derived from local
    diagonal dominance.

    This wrapper removes the last explicit determinant hypothesis from the
    determinant-facing route.  The previous transposed determinant follows from
    the top-left part of the same diagonally-dominant leading block, while the
    current determinant follows directly from `IsDiagDominantUpper`.  The
    previous-column lower-zero shape remains visible because the trailing-norm
    nonbreakdown bridge still uses it. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef
      (StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds
        hmn fp A_hat b_hat alpha Ucap hm hDD hUcap_nonneg
        hAlphaDef hlowerPrev hu huCap hsmall)
/-- Solver-facing canonical rational-gamma stored-QR certificate with the
    previous-column lower-zero shape derived from the stored panel recurrence.

    Compared with
    `..._diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`,
    this wrapper removes the explicit `hlowerPrev` hypothesis: the stored
    Householder panel update preserves completed columns and writes exact zeros
    below each pivot, so the lower-zero shape follows from `hStepA`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 :=
    storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
      fp hmn A_hat alpha hStepA
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds
      fp hmn A b A_hat b_hat alpha Ucap hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hDD hUcap_nonneg hlowerPrev hu huCap hsmall
/-- Solver-facing stored-lower canonical rational-gamma certificate with the
    nonnegativity of `Ucap` derived from the unit-roundoff cap.

    This is the same certificate as
    `..._diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds`,
    but it removes the separate `0 ≤ Ucap` hypothesis: since the FP model has
    `0 ≤ fp.u`, the assumption `fp.u ≤ Ucap` already implies `0 ≤ Ucap`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hUcap_nonneg : 0 ≤ Ucap := le_trans fp.u_nonneg hu
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds
      fp hmn A b A_hat b_hat alpha Ucap hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hDD hUcap_nonneg hu huCap hsmall
/-- Solver-facing stored-lower canonical rational-gamma certificate with all
    operation-validity guards derived from the displayed unit-roundoff cap.

The assumptions `fp.u ≤ Ucap` and `(m : ℝ) * Ucap < 1` imply
`gammaValid fp m`; since `n ≤ m`, they also imply `gammaValid fp n`. Thus the
public cap-based statement does not need separate gamma-validity hypotheses. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Ucap : ℝ)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m Ucap hu huCap
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap
      fp hmn A b A_hat b_hat alpha Ucap hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hu huCap hsmall
/-- Solver-facing stored-lower canonical rational-gamma certificate specialized
    to the actual unit roundoff of the FP model.

This removes the displayed-cap field `fp.u ≤ Ucap` by choosing
`Ucap = fp.u`.  The ordinary validity guard `gammaValid fp m` is still visible,
and the canonical scalar smallness condition is evaluated at the actual
unit roundoff. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have huCap : (m : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid
      fp hmn A b A_hat b_hat alpha fp.u hInitA hInitb hStepA hStepb
      hAlphaDef hDD (le_rfl : fp.u ≤ fp.u) huCap hsmall
/-- Solver-facing stored-lower canonical rational-gamma certificate specialized
    to the actual unit roundoff, with the operation-validity guard displayed as
    the scalar condition `(m : ℝ) * fp.u < 1`.

This is the source-facing sibling of
`..._of_actualUnitRoundoff`: it replaces the abstract `gammaValid fp m`
hypothesis by the scalar guard from which the needed `gammaValid` facts are
derived.  The canonical scalar smallness inequality remains visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid
      fp hmn A b A_hat b_hat alpha fp.u hInitA hInitb hStepA hStepb
      hAlphaDef hDD (le_rfl : fp.u ≤ fp.u) huSmall hsmall
/-- Solver-facing stored-QR certificate from local diagonal dominance and
    pointwise bounds on the three scalar route families.

    This is the pointwise-bound sibling of
    `..._leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`.
    It keeps the remaining route-1 QR obligations visible as displayed constants
    `Dmax`, `Cmax`, and `Nmax`: every local diagonal-dominant inverse factor,
    every stored compact Householder norm coefficient, and every displayed pivot
    column norm must be bounded by those constants, and the corresponding scalar
    smallness inequality must hold. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Dmax Cmax Nmax : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hDmax_nonneg : 0 ≤ Dmax)
    (hCmax_nonneg : 0 ≤ Cmax)
    (hNmax_nonneg : 0 ≤ Nmax)
    (hD : ∀ k : Fin n,
      diagDominantUpperInvBudgetExpr (k.val + 1)
        (qrLeadingBlock (A_hat k.val)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le k.isLt hmn)) k.isLt)
        ⟨k.val, Nat.lt_succ_self k.val⟩ ≤ Dmax)
    (hC : ∀ k : Fin n,
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤ Cmax)
    (hN : ∀ k : Fin n,
      vecNorm2 (fun i : Fin m => A_hat k.val i k) ≤ Nmax)
    (hsmall :
      2 * Dmax *
          ((m : ℝ) *
            (((n : ℝ) * ((n : ℝ) * Cmax + Cmax)) * Nmax) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hproduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1 :=
    storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds
      hmn fp A_hat b_hat alpha Dmax Cmax Nmax hm
      (fun k => hDD k.val k.isLt)
      hDmax_nonneg hCmax_nonneg hNmax_nonneg hD hC hN hsmall
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hDD ?_
  intro k hk
  exact
    lt_of_le_of_lt
      (storedQRCompactSequenceProductExpr_le_budget hmn fp A_hat b_hat alpha
        (⟨k, hk⟩ : Fin n))
      hproduct
/-- Concrete-dual pointwise-bound stored-QR certificate with determinant
    nonzeroness derived from `IsDiagDominantUpper`.

    This wrapper removes only the explicit determinant hypothesis from the
    previous theorem.  The diagonal-dominance and pointwise scalar-route bounds
    remain visible as source/domain obligations. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (Dmax Cmax Nmax : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hDmax_nonneg : 0 ≤ Dmax)
    (hCmax_nonneg : 0 ≤ Cmax)
    (hNmax_nonneg : 0 ≤ Nmax)
    (hD : ∀ k : Fin n,
      diagDominantUpperInvBudgetExpr (k.val + 1)
        (qrLeadingBlock (A_hat k.val)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le k.isLt hmn)) k.isLt)
        ⟨k.val, Nat.lt_succ_self k.val⟩ ≤ Dmax)
    (hC : ∀ k : Fin n,
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤ Cmax)
    (hN : ∀ k : Fin n,
      vecNorm2 (fun i : Fin m => A_hat k.val i k) ≤ Nmax)
    (hsmall :
      2 * Dmax *
          ((m : ℝ) *
            (((n : ℝ) * ((n : ℝ) * Cmax + Cmax)) * Nmax) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual
      fp hmn A b A_hat b_hat alpha Dmax Cmax Nmax hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef
      (fun k hk =>
        det_ne_zero_of_diagDominantUpper (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (hDD k hk))
      hDD hDmax_nonneg hCmax_nonneg hNmax_nonneg hD hC hN hsmall
/-- Solver-facing QR certificate with the triangular shape derived from the
    stored recurrence.

    Compared with `..._sourceOffDiagonalControl`, this theorem no longer asks
    the caller to prove the upper-triangular leading-block field.  That field
    follows from the repository's stored Householder prefix-lower-zero theorem.
    The remaining visible obligations are the source-specific nonzero diagonal,
    row-wise off-diagonal domination, and compact-product smallness fields. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diag_offdiag_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdiag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i ≠ 0)
    (hoffdiag : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product
        hmn fp A_hat b_hat alpha hStepA hdiag hoffdiag hproduct)
/-- Solver-facing QR certificate with stored triangular shape and stored
    previous-diagonal nonzeros derived from the signed-alpha nonbreakdown
    budget.

    This narrows the nonzero-diagonal part of the route-1 bottleneck: the
    theorem keeps only the current pivot nonzero condition visible, while the
    previous displayed diagonals are supplied by the repository's stored
    prefix-diagonal theorem.  Row-wise off-diagonal domination and
    compact-product smallness remain explicit source/domain assumptions. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_pivot_sqrtBudget_offdiag_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hdiagPivot : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0)
    (hoffdiag : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product
        hmn fp A_hat b_hat alpha hm hStepA hAlphaDef hbudgetSqrt
        hdiagPivot hoffdiag hproduct)
/-- Solver-facing QR certificate with the current pivot condition derived from
    nonsingular displayed leading blocks.

    This is the determinant-shaped companion to
    `..._signed_alpha_pivot_sqrtBudget_offdiag_product`.  It keeps the same
    square-root nonbreakdown, row-wise off-diagonal domination, and
    compact-product smallness hypotheses, but replaces the raw current-pivot
    nonzero assumption by the source-shaped local determinant condition. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩)))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiag : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product
        hmn fp A_hat b_hat alpha hm hStepA hAlphaDef hbudgetSqrt
        hdetLead hoffdiag hproduct)
/-- Solver-facing QR certificate from source-shaped off-diagonal control with
    the square-root nonbreakdown budget supplied by a dimensioned
    trailing-norm-square margin.

    This is the determinant/norm-square companion to
    `..._leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`.  It exposes the
    more algebraic condition `m * budget^2 < ||active column||_2^2` and reuses
    the local norm-square-to-square-root bridge before applying the existing
    source-shaped QR certificate. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_offdiag_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiag : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product
        hmn fp A_hat b_hat alpha hm hStepA hAlphaDef hbudgetNormSq
        hdetLead hoffdiag hproduct)
/-- Solver-facing QR certificate with off-diagonal control supplied through
    row-growth budgets and diagonal lower bounds.

    This is the Cox--Higham-facing companion to
    `..._leadingBlock_det_ne_zero_normSqBudget_offdiag_product`: instead of
    assuming row-wise off-diagonal domination directly, it asks for a row
    budget on each displayed upper entry and a lower bound showing that this
    budget is dominated by the displayed diagonal magnitude. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiagBudget : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product
        hmn fp A_hat b_hat alpha rowBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hoffdiagBudget hrowBudget_diag hproduct)
/-- Solver-facing QR certificate with row-growth budgets whose diagonal
    lower-bound obligation is restricted to rows with displayed upper entries.

    Compared with
    `..._leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`, this theorem
    does not ask for the unused comparison on the final row `i = k` of the
    `(k+1) × (k+1)` leading block: no strict upper off-diagonal entry starts in
    that row. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiagBudget : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows
        hmn fp A_hat b_hat alpha rowBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hoffdiagBudget hrowBudget_diag hproduct)
/-- Stored trailing Householder QR solve certificate from Cox--Higham stage
    budgets and diagonal lower bounds.

    This composes the QR-layer row-growth bridge with the row-budget source
    control theorem, then feeds the resulting `StoredQRSourceOffDiagonalControl`
    into the existing least-squares QR backward-error certificate.  It is still
    a scoped bottleneck dependency: concrete signed-pivot policies must supply
    the stage-budget/pivot-zeroing fields and the diagonal lower-bound
    nonbreakdown field. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStageStep : ∀ t, t < n →
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t (v t) (beta t) (A_hat t))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m (householder m (v t) (beta t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m (v t) (beta t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m (householder m (v t) (beta t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product
        hmn fp A_hat b_hat alpha v beta c rowBudget entryBudget hm
        hStepA hStageStep hAlphaDef hbudgetNormSq hdetLead hinit hpivot
        hbudget hexact hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing QR certificate from Cox--Higham stage budgets whose diagonal
    lower-bound field is restricted to rows that have displayed upper entries.

    This composes the corrected source-control stage-budget wrapper
    `..._stageBudget_rowBudget_product_of_offdiag_rows` with the existing
    least-squares QR backward-error certificate. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStageStep : ∀ t, t < n →
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t (v t) (beta t) (A_hat t))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m (householder m (v t) (beta t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m (v t) (beta t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m (householder m (v t) (beta t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows
        hmn fp A_hat b_hat alpha v beta c rowBudget entryBudget hm
        hStepA hStageStep hAlphaDef hbudgetNormSq hdetLead hinit hpivot
        hbudget hexact hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing QR certificate from Cox--Higham stage budgets for the
    concrete signed stored-QR stages.

    This is the signed-stage specialization of the stage-budget handoff above:
    the remaining visible proof obligations are now exactly the Cox--Higham
    fields for the signed stored-QR loop, plus the diagonal lower-bound and
    compact-product assumptions needed by the local QR solve certificate. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m
              (householder m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product
        hmn fp A_hat b_hat alpha c rowBudget entryBudget hm hStepA
        hAlphaDef hbudgetNormSq hdetLead hinit hpivot hbudget hexact
        hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing signed-stage QR certificate whose diagonal lower-bound field
    is restricted to rows that can contribute displayed strict upper entries. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m
              (householder m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_offdiag_rows
        hmn fp A_hat b_hat alpha c rowBudget entryBudget hm hStepA
        hAlphaDef hbudgetNormSq hdetLead hinit hpivot hbudget hexact
        hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing QR certificate from signed-stage Cox--Higham budgets, with
    pivot-column zeroing derived from the norm-square nonbreakdown budget.

    This is the solver-level wrapper around
    `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`.
    The explicit pivot-zeroing field is no longer a hypothesis; the remaining
    visible bottleneck fields are stage-budget recurrence, exact same-reflector
    bounds, row-budget diagonal lower bounds, determinant/nonbreakdown data,
    and compact-product smallness. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget
        hmn fp A_hat b_hat alpha c rowBudget entryBudget hm hStepA
        hAlphaDef hbudgetNormSq hdetLead hinit hbudget hexact
        hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing signed-stage QR certificate with norm-square-derived
    pivot-zeroing and offdiag-row-only diagonal lower-bound obligations. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i)
    (hrowBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        rowBudget k hk i ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget_offdiag_rows
        hmn fp A_hat b_hat alpha c rowBudget entryBudget hm hStepA
        hAlphaDef hbudgetNormSq hdetLead hinit hbudget hexact
        hrowBudget hrowBudget_diag hproduct)
/-- Solver-facing QR certificate from a single monotone signed-stage
    Cox--Higham budget sequence.

    This removes the terminal `hrowBudget` field from the signed-stage solver
    handoff by using the monotone budget `stageBudget k` as the displayed
    row budget for the `k`th leading block.  The remaining visible fields are
    the stage recurrence/exact same-reflector bounds, diagonal lower bounds
    `stageBudget k <= |S_k ii|`, determinant/norm-square nonbreakdown, and
    compact-product smallness. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget
        hmn fp A_hat b_hat alpha c stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hbudget hexact hBudget_mono
        hBudget_diag hproduct)
/-- Solver-facing uniform signed-stage QR certificate with offdiag-row-only
    diagonal lower-bound obligations. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_offdiag_rows
        hmn fp A_hat b_hat alpha c stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hbudget hexact hBudget_mono
        hBudget_diag hproduct)
/-- Solver-facing QR certificate from a single monotone signed-stage
    Cox--Higham budget sequence, deriving the exact-reflector field from
    concrete signed-stage row/column bounds.

    This is the solver wrapper around
    `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`.
    It removes the abstract `hexact` field from the uniform-stage-budget
    theorem while still leaving diagonal lower bounds, determinant/norm-square
    nonbreakdown, pivot maximality, stage entry bounds, and compact-product
    smallness visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        coxHighamActiveRowGrowthFactor m * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hstageRowBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
      ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        ∀ l : Fin n, t ≤ l.val →
          |A_hat t
            (qrLeadingRow m k
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i) l| ≤
            stageBudget t)
    (hstageColBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
      ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        ∀ r : Fin m, t ≤ r.val →
          |A_hat t r (qrLeadingColumn n k hk j)| ≤ stageBudget t)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hbudget hBudget_nonneg hBudget_mono
        hBudget_diag hpivotMax hstageRowBound hstageColBound hproduct)
/-- Solver-facing uniform signed-stage QR certificate deriving exact-reflector
    bounds from concrete stage row/column bounds, with offdiag-row-only
    diagonal lower-bound obligations. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        coxHighamActiveRowGrowthFactor m * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hstageRowBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
      ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        ∀ l : Fin n, t ≤ l.val →
          |A_hat t
            (qrLeadingRow m k
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i) l| ≤
            stageBudget t)
    (hstageColBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
      ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        ∀ r : Fin m, t ≤ r.val →
          |A_hat t r (qrLeadingColumn n k hk j)| ≤ stageBudget t)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hbudget hBudget_nonneg hBudget_mono
        hBudget_diag hpivotMax hstageRowBound hstageColBound hproduct)
/-- Solver-facing uniform signed-stage QR certificate from an active-suffix
    block budget plus a prefix-row budget.

    This is the propagated form of the active/prefix split: active-stage row
    and column entry bounds are supplied by one suffix block invariant, while
    prefix displayed rows remain an explicit source obligation. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        coxHighamActiveRowGrowthFactor m * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hstageActiveBlockBound : ∀ t, t < n →
      ∀ r : Fin m, t ≤ r.val →
        ∀ l : Fin n, t ≤ l.val → |A_hat t r l| ≤ stageBudget t)
    (hstagePrefixRowBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
      ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        ∀ l : Fin n, t ≤ l.val →
          (qrLeadingRow m k
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i).val < t →
            |A_hat t
              (qrLeadingRow m k
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i) l| ≤
              stageBudget t)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
        (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows
          hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
          hbudgetNormSq hdetLead hinit hbudget hBudget_nonneg hBudget_mono
          hBudget_diag hpivotMax hstageActiveBlockBound hstagePrefixRowBound hproduct)
  /-- Solver-facing uniform signed-stage QR certificate deriving the active-suffix
      block budget from the signed-pivot active-block recurrence.

      This closes the active-suffix part of the active/prefix split at the
      solver-facing level: the remaining stage-entry source obligation is the
      prefix displayed-row budget, while the active block is propagated by the
      Cox--Higham recurrence theorem. -/
  theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows
      {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
      (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
      (A_hat : ℕ → Fin m → Fin n → ℝ)
      (b_hat : ℕ → Fin m → ℝ)
      (alpha : ℕ → ℝ)
      (stageBudget : ℕ → ℝ)
      (hm : gammaValid fp m)
      (hγ : gammaValid fp n)
      (hInitA : A_hat 0 = A)
      (hInitb : b_hat 0 = b)
      (hStepA : ∀ k (hk : k < n),
        A_hat (k + 1) =
          fl_householderStoredPanelStep fp m n k
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (A_hat k))
      (hStepb : ∀ k (hk : k < n),
        b_hat (k + 1) =
          fl_householderStoredRhsStep fp m k
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (b_hat k))
      (hAlphaDef : ∀ k (hk : k < n),
        alpha k =
          signedHouseholderAlpha
            (Real.sqrt
              (householderTrailingNorm2Sq m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩)))
            (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
      (hbudgetNormSq : ∀ k (hk : k < n),
        (m : ℝ) *
            (householderCompactComponentBudget fp m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
              (householderBetaSpec m
                (householderTrailingActiveVector m
                  ⟨k, lt_of_lt_of_le hk hmn⟩
                  (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
              (fun a => A_hat k a ⟨k, hk⟩)
              ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
          householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩))
      (hdetLead : ∀ k (hk : k < n),
        Matrix.det
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
      (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
        |A_hat 0
            (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
            (qrLeadingColumn n k hk j)| ≤
          stageBudget 0)
      (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
        |A_hat 0 r l| ≤ stageBudget 0)
      (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
        ∀ t : ℕ, t < qrLeadingOffdiagStop j →
          coxHighamActiveRowGrowthFactor m * stageBudget t +
              householderCompactComponentBudget fp m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t)
                (fun a => A_hat t a (qrLeadingColumn n k hk j))
                (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
            ≤ stageBudget (t + 1))
      (hactiveBudget : ∀ t : ℕ, t + 1 < n →
        ∀ r : Fin m, t + 1 ≤ r.val →
          ∀ l : Fin n, t + 1 ≤ l.val →
            coxHighamActiveRowGrowthFactor m * stageBudget t +
                householderCompactComponentBudget fp m
                  (storedQRSignedStageVector hmn A_hat alpha t)
                  (storedQRSignedStageBeta hmn A_hat alpha t)
                  (fun a => A_hat t a l) r ≤
              stageBudget (t + 1))
      (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
      (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
      (hBudget_diag : ∀ k (hk : k < n),
        ∀ i : Fin (k + 1), i.val < k →
          stageBudget k ≤
          |qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
      (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
          householderTrailingColumnNorm2Sq
              (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
              (A_hat t) l ≤
            householderTrailingColumnNorm2Sq
              (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
              (A_hat t) ⟨t, ht⟩)
      (hcompleted : ∀ t (_ht : t < n), ∀ j : Fin n, j.val < t →
        ∀ i : Fin m,
          matMulVec m
            (householder m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t))
            (fun a => A_hat t a j) i = A_hat t i j)
      (hstagePrefixRowBound : ∀ k (hk : k < n), ∀ i j : Fin (k + 1),
        ∀ _hij : i.val < j.val, ∀ t : ℕ, t < qrLeadingOffdiagStop j →
          ∀ l : Fin n, t ≤ l.val →
            (qrLeadingRow m k
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i).val < t →
              |A_hat t
                (qrLeadingRow m k
                  (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i) l| ≤
                stageBudget t)
      (hproduct : ∀ k (hk : k < n),
        2 *
            diagDominantUpperInvBudgetExpr (k + 1)
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
              ⟨k, Nat.lt_succ_self k⟩ *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
          1) :
      let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
      let R : Fin n → Fin n → ℝ :=
        fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
      LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
        (fl_backSub fp n R
          (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
        (qrSolveFinalGramBudget fp A R cStep)
        (qrSolveFinalRhsBudget fp A b R cStep) := by
    exact
      LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
        fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
        hAlphaDef
        (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows
          hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
          hbudgetNormSq hdetLead hinit hinitBlock hbudget hactiveBudget
          hBudget_nonneg hBudget_mono hBudget_diag hpivotMax hcompleted
          hstagePrefixRowBound hproduct)
/-- Solver-facing uniform signed-stage QR certificate deriving both active
    suffix and prefix displayed-row stage-entry bounds from one-step
    recurrences.

    This is the solver-level version of the active/prefix recurrence handoff:
    the active trailing block is propagated by the signed-pivot active-block
    recurrence, and the displayed prefix rows are propagated by the prefix-row
    recurrence. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        coxHighamActiveRowGrowthFactor m * stageBudget t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ stageBudget (t + 1))
    (hactiveBudget : ∀ t : ℕ, t + 1 < n →
      ∀ r : Fin m, t + 1 ≤ r.val →
        ∀ l : Fin n, t + 1 ≤ l.val →
          coxHighamActiveRowGrowthFactor m * stageBudget t +
              householderCompactComponentBudget fp m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t)
                (fun a => A_hat t a l) r ≤
            stageBudget (t + 1))
    (hprefixBudget : ∀ t (_ht : t < n),
      ∀ r : Fin m, r.val < t + 1 →
        ∀ l : Fin n, t ≤ l.val →
          coxHighamActiveRowGrowthFactor m * stageBudget t +
              householderCompactComponentBudget fp m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t)
                (fun a => A_hat t a l) r ≤
            stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hcompleted : ∀ t (_ht : t < n), ∀ j : Fin n, j.val < t →
      ∀ i : Fin m,
        matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a j) i = A_hat t i j)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hbudget hactiveBudget
        hprefixBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
        hcompleted hproduct)
/-- Solver-facing uniform signed-stage QR certificate whose one-step
    off-diagonal, active-block, and prefix-row budget fields are all supplied
    by a finite global compact-step budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hcompleted : ∀ t (_ht : t < n), ∀ j : Fin n, j.val < t →
      ∀ i : Fin m,
        matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a j) i = A_hat t i j)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_mono hBudget_diag hpivotMax hcompleted
        hproduct)
/-- Solver-facing global compact-budget QR certificate with completed-column
    preservation derived from the stored QR lower-zero invariant. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_mono hBudget_diag hpivotMax hproduct)
/-- Solver-facing global compact-budget QR certificate whose compact-product
    side condition is supplied by one finite global product budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_mono hBudget_diag hpivotMax hglobalProduct)
/-- Solver-facing completed-column global-product QR certificate without a
    separate global stage-budget monotonicity hypothesis. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_diag hpivotMax hglobalProduct)
/-- Solver-facing global-product QR certificate with norm-square
    nonbreakdown derived from local `κ∞`/dual-budget data.

    This is the active/prefix global-budget route with the raw
    `hbudgetNormSq` field removed.  The remaining visible assumptions are the
    local leading-block determinants, the `κ∞`/self-norm and dual compact
    budgets that imply the norm-square margin, the off-diagonal row budget
    lower bounds, and the finite global product condition. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
        hmn fp A_hat b_hat alpha κ K stageBudget hm hStepA hAlphaDef
      hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
      hglobalProduct)
/-- Solver-facing active/prefix global-product QR certificate with the
    diagonal lower-bound field supplied by one finite stage-diagonal defect
    budget.

This is the solver-level companion to
`StoredQRSourceOffDiagonalControl...stageDiagDefect_offdiag_rows`: it replaces
the family of row-wise diagonal lower-bound hypotheses by the scalar finite
condition `storedQRStageDiagLowerDefectBudget <= 0`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hstageDiagDefect :
      storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef
        hbudgetNormSq hdetLead hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_mono hstageDiagDefect hpivotMax
        hglobalProduct)
/-- Solver-facing kappa/dual-budget active-prefix QR certificate with the
    diagonal lower-bound field supplied by the finite stage-diagonal defect
    budget. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hstageDiagDefect :
      storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
        hmn fp A_hat b_hat alpha κ K stageBudget hm hStepA hAlphaDef
        hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
        hglobalBudget hBudget_nonneg hBudget_mono hstageDiagDefect
        hpivotMax hglobalProduct)
/-- Active-max-pivot variant of the solver-facing global-product QR certificate.

The preceding theorem exposes a raw pivot-maximality inequality.  This wrapper
uses the finite active pivot selector
`householderActiveMaxPivotColumn` instead, deriving the raw maximality field
from `householderActiveMaxPivotColumn_pivot_max` before applying the existing
solver theorem.  The diagonal row-budget lower-bound hypothesis is still
visible; this theorem only closes the pivot-policy dependency. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hBudget_diag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget k ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  classical
  have hpivotMax : ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) ⟨t, ht⟩ := by
    intro t ht l hl
    have hmax :=
      householderActiveMaxPivotColumn_pivot_max
        ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t) l hl
    have hnormEq :
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t)
            (householderActiveMaxPivotColumn
              ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t)) =
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩ := by
      rw [← hpivotChoice t ht]
    exact hmax.trans_eq hnormEq
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
      fp hmn A b A_hat b_hat alpha κ K stageBudget hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit
      hinitBlock hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag
      hpivotMax hglobalProduct
/-- Solver-facing active-max-pivot sibling of the stage-diagonal defect route.

This theorem combines the two latest active/prefix reductions: the offdiag-row
diagonal lower-bound family is supplied by the finite scalar
`storedQRStageDiagLowerDefectBudget <= 0`, and raw pivot maximality is supplied
by the finite active pivot policy `householderActiveMaxPivotColumn`. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hstageDiagDefect :
      storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows
        hmn fp A_hat b_hat alpha κ K stageBudget hm hStepA hAlphaDef
        hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
        hglobalBudget hBudget_nonneg hBudget_mono hstageDiagDefect
        hpivotChoice hglobalProduct)
/-- Solver-facing diagonal-dominant scalar-comparison sibling of the
    active-max-pivot route.

This wrapper removes the separate leading-block determinant and row-max scalar
defect assumptions from the scalar-comparison active-pivot surface when local
diagonal dominance is supplied. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows
        hmn fp A_hat b_hat alpha κ K stageBudget hm hStepA hAlphaDef
        hDD hK hκ hκbudget hbudgetDual hinit hinitBlock hglobalBudget
        hBudget_nonneg hBudget_mono hcomparison hpivotChoice hglobalProduct)
/-- Solver-facing diagonal-dominant scalar-comparison sibling whose compact
    product hypothesis is supplied by the canonical finite-max smallness
    inequality.

This is the local QR/preconditioner handoff corresponding to
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_..._finiteMaxSmallness_...`:
the raw global product field is derived internally from local diagonal
dominance and the canonical finite-max scalar. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1 :=
    storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness
      hmn fp A_hat b_hat alpha hm (fun k => hDD k.val k.isLt) hsmall
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows
      fp hmn A b A_hat b_hat alpha κ K stageBudget hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hDD hK hκ hκbudget hbudgetDual hinit
      hinitBlock hglobalBudget hBudget_nonneg hBudget_mono hcomparison
      hpivotChoice hglobalProduct
/-- Solver-facing active diagonal-dominant scalar-comparison theorem using the
    concrete dual-budget route.

This is the local QR/preconditioner handoff that removes the auxiliary `κ`/`K`
and dual compact-budget package from the active finite-max scalar-comparison
branch.  The remaining visible QR-domain fields are local diagonal dominance,
the signed-stage recurrence budget, active-pivot policy, scalar comparison
defect, and the canonical finite-max product smallness scalar. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget hm hStepA hAlphaDef hDD hinit
        hinitBlock hglobalBudget hBudget_nonneg hBudget_mono hcomparison
        hpivotChoice hsmall)
/-- Actual-unit-roundoff sibling of the solver-facing active finite-max
    concrete-dual theorem.

The local and triangular `gammaValid` guards are derived from
`(m : ℝ) * fp.u < 1`.  The remaining visible QR-domain fields are unchanged:
local diagonal dominance, signed-stage recurrence budgets, active-pivot choice,
the scalar comparison defect, and finite-max product smallness. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hsmall :
      2 * storedQRDiagDominantInvFactorBudget hmn A_hat *
          ((m : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
              storedQRPivotColumnNormBudget hmn A_hat) ^ 2) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
      fp hmn A b A_hat b_hat alpha stageBudget hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice hsmall
/-- Solver-facing active diagonal-dominant scalar-comparison theorem using the
    canonical source-denominator/rational-gamma compact-product cap.

This is the local QR/preconditioner handoff for the active scalar-comparison
branch after replacing the assembled finite-max product scalar by a
source-denominator nonbreakdown field, a unit-roundoff cap, and the canonical
rational-gamma cap-smallness inequality. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
        hmn fp A_hat b_hat alpha stageBudget Ucap hm hStepA hAlphaDef hDD
        hinit hinitBlock hglobalBudget hBudget_nonneg hBudget_mono
        hcomparison hpivotChoice hUcap_nonneg hden hu huCap hsmall)
/-- Solver-facing active source-denominator/cap theorem with horizon-clamped
    stage-budget monotonicity.

The finite stored-QR recurrence supplies the monotonicity needed by the
source-control handoff after clamping the stage budget at the QR horizon, so
the source-facing hypotheses no longer need to include a global
`hBudget_mono` field. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (Ucap : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (m : ℝ) * Ucap < 1)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * Ucap) / (1 - (m : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
        hmn fp A_hat b_hat alpha stageBudget Ucap hm hStepA hAlphaDef hDD
        hinit hinitBlock hglobalBudget hBudget_nonneg hcomparison
        hpivotChoice hUcap_nonneg hden hu huCap hsmall)
/-- Actual-unit-roundoff sibling of the solver-facing active
    source-denominator/cap theorem.

The local and triangular `gammaValid` guards are derived from
`(m : ℝ) * fp.u < 1`; the source denominator, diagonal dominance,
active-pivot, scalar comparison, recurrence, and actual-unit scalar-smallness
fields remain visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
      fp hmn A b A_hat b_hat alpha stageBudget fp.u hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hDD hinit hinitBlock hglobalBudget
      hBudget_nonneg hBudget_mono hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall
/-- Solver-facing actual-unit-roundoff source-denominator theorem with
    horizon-clamped stage-budget monotonicity.

This combines the actual-unit specialization with the horizon-budget route:
`gammaValid` is derived from `(m : ℝ) * fp.u < 1`, and the global
stage-budget monotonicity required by the source-control handoff is derived
from the finite stored-QR recurrence. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
      fp hmn A b A_hat b_hat alpha stageBudget fp.u hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hDD hinit hinitBlock hglobalBudget
      hBudget_nonneg hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall
/-- Solver-facing actual-unit active source-denominator theorem with denominator
    nonbreakdown derived from the stored loop.

This stored-lower sibling removes the raw denominator hypothesis from the
active scalar-comparison solver surface.  The remaining visible fields are the
actual-unit scalar guard and scalar smallness, local diagonal dominance,
signed-stage recurrence budget, active-pivot choice, and comparison defect. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
      fp hmn A b A_hat b_hat alpha stageBudget huSmall hInitA hInitb
      hStepA hStepb hAlphaDef hDD hinit hinitBlock hglobalBudget
      hBudget_nonneg hBudget_mono hcomparison hpivotChoice
      (storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
        fp hmn A_hat alpha hStepA hAlphaDef hDD)
      hsmall
/-- Solver-facing stored-lower actual-unit route with horizon-clamped
    stage-budget monotonicity.

This combines the stored-loop denominator derivation with the existing
actual-unit horizon-budget source-denominator theorem, so neither the raw
source denominator nor global `hBudget_mono` is visible at this surface. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hsmall :
      let Dcap := storedQRDiagDominantInvFactorBudget hmn A_hat
      let Ncap := storedQRPivotColumnNormBudget hmn A_hat
      let Gcap := ((m : ℝ) * fp.u) / (1 - (m : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((m : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
        hmn fp A_hat b_hat alpha stageBudget huSmall hStepA hAlphaDef hDD
        hinit hinitBlock hglobalBudget hBudget_nonneg hcomparison
        hpivotChoice hsmall)
/-- Solver-facing active-max-pivot QR certificate using row-max scalar defect
    plus an explicit stage-budget/row-max comparison.

This is the visible-assumption solver surface for the LS.2g-gi bridge: the
caller supplies the row-max scalar defect and the comparison
`stageBudget <= rowMax`, and the wrapper derives the scalar stage-diagonal
condition internally before applying the active-pivot stage-diagonal route. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hrowDefect : storedQRRowMaxDiagDefectBudget hmn A_hat ≤ 0)
    (hstage_le_rowMax : ∀ k (hk : k < n), ∀ i : Fin (k + 1), i.val < k →
      stageBudget k ≤ qrLeadingStrictUpperRowMaxBudget hmn A_hat k hk i)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl
      fp hmn A b A_hat b_hat alpha hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef
      (StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
        hmn fp A_hat b_hat alpha κ K stageBudget hm hStepA hAlphaDef
      hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      hstage_le_rowMax hpivotChoice hglobalProduct)
/-- Solver-facing active-max-pivot row-max QR certificate with the
    operation-validity guard displayed as `(m : ℝ) * fp.u < 1`.

This is the actual-unit-roundoff sibling of the visible row-max active-pivot
solver theorem above.  It derives the local `gammaValid fp m` and triangular
`gammaValid fp n` obligations internally, while keeping the row-max scalar
defect, stage-budget/row-max comparison, determinant/conditioning, dual
compact-budget, and global compact-product hypotheses visible. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hrowDefect : storedQRRowMaxDiagDefectBudget hmn A_hat ≤ 0)
    (hstage_le_rowMax : ∀ k (hk : k < n), ∀ i : Fin (k + 1), i.val < k →
      stageBudget k ≤ qrLeadingStrictUpperRowMaxBudget hmn A_hat k hk i)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  have hm : gammaValid fp m :=
    gammaValid_of_u_le_cap fp m fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
      fp hmn A b A_hat b_hat alpha κ K stageBudget hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      hstage_le_rowMax hpivotChoice hglobalProduct
/-- Solver-facing active-max-pivot QR certificate using the row-max scalar
    defect and scalar stage-budget/row-max comparison defect.

This is the finite-defect version of the visible row-max solver surface: it
derives the old displayed comparison from
`storedQRStageRowMaxComparisonDefectBudget <= 0` before applying the pointwise
row-max theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hrowDefect : storedQRRowMaxDiagDefectBudget hmn A_hat ≤ 0)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows
      fp hmn A b A_hat b_hat alpha κ K stageBudget hm hγ hInitA hInitb
      hStepA hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit
      hinitBlock hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
        hmn A_hat stageBudget hcomparison)
      hpivotChoice hglobalProduct
/-- Actual-unit-roundoff sibling of the solver-facing scalar-comparison
    active-max-pivot row-max theorem. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha κ K : ℕ → ℝ)
    (stageBudget : ℕ → ℝ)
    (huSmall : (m : ℝ) * fp.u < 1)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hκ : ∀ k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ k)
    (hκbudget : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ k /
            infNorm
              (qrLeadingBlock (A_hat k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K k)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget 0)
    (hinitBlock : ∀ r : Fin m, ∀ l : Fin n,
      |A_hat 0 r l| ≤ stageBudget 0)
    (hglobalBudget : ∀ t (ht : t < n),
      coxHighamActiveRowGrowthFactor m * stageBudget t +
          storedQRSignedStageGlobalCompactBudget hmn fp A_hat alpha t ht ≤
        stageBudget (t + 1))
    (hBudget_nonneg : ∀ t : ℕ, 0 ≤ stageBudget t)
    (hBudget_mono : ∀ a b : ℕ, a ≤ b → stageBudget a ≤ stageBudget b)
    (hrowDefect : storedQRRowMaxDiagDefectBudget hmn A_hat ≤ 0)
    (hcomparison :
      storedQRStageRowMaxComparisonDefectBudget hmn A_hat stageBudget ≤ 0)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t))
    (hglobalProduct :
      storedQRCompactSequenceProductBudget hmn fp A_hat b_hat alpha < 1) :
    let cStep := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n R
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      (qrSolveFinalGramBudget fp A R cStep)
      (qrSolveFinalRhsBudget fp A b R cStep) := by
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid
      fp hmn A b A_hat b_hat alpha κ K stageBudget huSmall hInitA hInitb
      hStepA hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit
      hinitBlock hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
        hmn A_hat stageBudget hcomparison)
      hpivotChoice hglobalProduct
  /-- Stored trailing Householder QR solve certificate from diagonally dominant
      local leading blocks with Higham's triangular inverse ∞-norm budget.

    This composes the local `InverseBounds` theorem
    `triInv_infNorm_sq_budget_of_diagDominantUpper` with the existing inverse
    ∞-norm QR route.  The remaining visible assumptions are source-domain
    assumptions for the concrete stored loop: local prefix-span nonbreakdown,
    sign choice, compact-update budgets, and final Gram/RHS norm budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hKbound : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (2 ^ k *
            (1 / Finset.inf' Finset.univ
              ⟨(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)), Finset.mem_univ _⟩
              (fun r : Fin (k + 1) =>
                |qrLeadingBlock (A_hat k)
                    (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk r r|))) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
      fp hmn A b A_hat b_hat alpha C K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha ?_ hprefixSpan hK ?_
      hsign hA_budget hb_budget hbudgetDual hG hg
  · intro k hk
    exact (hC k hk).1
  · intro k hk
    exact
      triInv_infNorm_sq_budget_of_diagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk)
        ⟨k, Nat.lt_succ_self k⟩
        (K k)
        (hDD k hk)
        (hC k hk)
        (by simpa using hKbound k hk)
/-- Stored trailing Householder QR solve certificate from diagonally dominant
    local leading blocks with nonzero determinant.

    This determinant-facing wrapper removes the explicit inverse witness from
    the diagonal-dominant triangular inverse route.  The inverse used in the
    budget is the repository nonsingular inverse of each local leading block,
    and `Matrix.det ≠ 0` supplies the two-sided inverse proof. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (K : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hKbound : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (2 ^ k *
            (1 / Finset.inf' Finset.univ
              ⟨(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)), Finset.mem_univ _⟩
              (fun r : Fin (k + 1) =>
                |qrLeadingBlock (A_hat k)
                    (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk r r|))) ^ 2 ≤
        K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k)
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  refine
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget
      fp hmn A b A_hat b_hat alpha
      (fun k hk =>
        nonsingInv (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
      K cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha ?_ hDD hprefixSpan hK hKbound
      hsign hA_budget hb_budget hbudgetDual hG hg
  intro k hk
  exact
    isInverse_nonsingInv_of_det_ne_zero (k + 1)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
      (hdetLead k hk)
/-- Stored trailing Householder QR solve certificate from nonsingular local
    leading blocks and a square-root trailing-norm pivot budget.

    This solver-facing wrapper composes the QR determinant/rank bridge with the
    existing stored-loop least-squares certificate.  The nonzero determinants
    of the previous and current leading blocks supply positive trailing-column
    norms; the square-root budget supplies the local pivot-error inequalities.
    Thus the remaining assumptions are visible local rank/triangular-solve
    domain conditions, sign choice, compact-update budget domination, and the
    final Gram/RHS norm budgets. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩)))
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩) := by
    intro k hk
    exact
      householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
        (A_hat k) (lt_of_lt_of_le hk hmn) hk
        (hdetPrev k hk) (hdetLead k hk) (hlowerPrev k hk)
  have hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k| := by
    intro k hk
    exact
      budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun i => A_hat k i ⟨k, hk⟩) (alpha k)
        (householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩)
        (halpha k hk) (hbudgetSqrt k hk)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha htrailingPos hsign
      hA_budget hb_budget hbudgetDiag hG hg
/-- Stored trailing Householder QR solve certificate through the explicit
    triangular-principal-minor route.

    This theorem composes the triangular determinant adapters with the
    solver-facing nonsingular-leading-block theorem.  It deliberately exposes
    the strong local domain assumptions: at each step the current panel has the
    upper-triangular shape on all subdiagonal entries used here, the previous
    and current leading principal diagonals are nonzero, and the local
    square-root pivot budget is small enough.  Thus this is a visible
    triangular-domain route, not the source-faithful theorem that ordinary full
    column rank alone preserves these leading principal minors. -/
theorem LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (cStep : ℝ) (hcStep : 0 ≤ cStep)
    (c_G c_g : ℝ)
    (hm : gammaValid fp m)
    (hγ : gammaValid fp n)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hupper : ∀ k (_hk : k < n) (i : Fin m) (j : Fin n),
      j.val < i.val → A_hat k i j = 0)
    (hdiagPrev : ∀ k (hk : k < n) (r : Fin k),
      A_hat k
        (qrPrefixRow m k (le_of_lt (lt_of_lt_of_le hk hmn)) r)
        (qrPreviousColumn n k hk r) ≠ 0)
    (hdiagLead : ∀ k (hk : k < n) (r : Fin (k + 1)),
      A_hat k
        (qrLeadingRow m k
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) r)
        (qrLeadingColumn n k hk r) ≠ 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        cStep * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        cStep * vecNorm2 (b_hat k))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩)))
    (hG : frobNorm
        (rectLSGramPerturbationNormBudget A
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))) ≤ c_G)
    (hg : ∀ j : Fin n,
      rectLSRhsPerturbationNormBudget A b
          (((1 + cStep) ^ n - 1) * frobNormRect A +
            gamma fp n *
              frobNormRect (rectTopBlock (m := m)
                (fun i j =>
                  A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)))
          (((1 + cStep) ^ n - 1) * vecNorm2 b) j ≤ c_g) :
    LSQRSolveBackwardError n (rectLSGram A) (rectLSRhs A b)
      (fl_backSub fp n
        (fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j)
        (fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩))
      c_G c_g := by
  classical
  have hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
    intro k hk
    exact
      qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) (le_of_lt (lt_of_lt_of_le hk hmn)) hk
        (hupper k hk) (hdiagPrev k hk)
  have hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    exact
      qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
        (hupper k hk) (hdiagLead k hk)
  have hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 := by
    intro k hk i j hki
    exact hupper k hk i (qrPreviousColumn n k hk j)
      (Nat.lt_of_lt_of_le j.isLt hki)
  exact
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget
      fp hmn A b A_hat b_hat alpha cStep hcStep c_G c_g hm hγ
      hInitA hInitb hStepA hStepb halpha hdetPrev hdetLead hlowerPrev
      hsign hA_budget hb_budget hbudgetSqrt hG hg

-- ============================================================
-- §19.2  Forward error from QR LS backward stability
-- ============================================================

end NumStability
