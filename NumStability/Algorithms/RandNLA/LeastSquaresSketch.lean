-- Algorithms/RandNLA/LeastSquaresSketch.lean
--
-- Deterministic least-squares consequences of a sketching/subspace-embedding
-- hypothesis, motivated by CACM RandNLA equation (8).
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.FiniteProbability
import NumStability.Algorithms.LeastSquares.LSNormalEquations
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.RandNLA.RowSamplingLeverage
import NumStability.Algorithms.RandNLA.RowSamplingLeverageMGF
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace NumStability

open scoped BigOperators

/-!
## Least-squares sketch objective

Equation (8) in the CACM RandNLA survey is the least-squares problem

`x_opt = argmin_x ||A x - b||₂`.

This file formalizes the deterministic implication used by RandNLA
least-squares algorithms: if a sketch preserves the squared residual objective
for every `x`, then an exact minimizer of the sketched problem is a relative
residual-objective approximation for the original problem.

It does not prove that a particular random sampling or random projection
constructs such a sketch with high probability.  That remains a separate
subspace-embedding/concentration obligation.
-/

/-- A vector is an additive-gap approximate minimizer of the least-squares
    objective.  The gap is intentionally explicit so later solver/preconditioner
    analyses can supply it without being hidden inside the sketch theorem. -/
def IsLeastSquaresApproxMinimizer {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (gap : ℝ) : Prop :=
  ∀ y : Fin n → ℝ, lsObjective A b x ≤ lsObjective A b y + gap

/-- Exact minimizers are approximate minimizers with zero additive gap. -/
theorem isLeastSquaresApproxMinimizer_of_minimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {x : Fin n → ℝ} (h : IsLeastSquaresMinimizer A b x) :
    IsLeastSquaresApproxMinimizer A b x 0 := by
  intro y
  simpa using h y

/-- A sketched least-squares instance preserves every squared residual objective
    within multiplicative factors `1 ± ε`. -/
def PreservesLSObjective {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ) (ε : ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    (1 - ε) * lsObjective A b x ≤ lsObjective SA Sb x ∧
      lsObjective SA Sb x ≤ (1 + ε) * lsObjective A b x

/-- Row-sampled least-squares matrix whose scaling probabilities are supplied
    by a basis matrix `U`.  This is the concrete Algorithm 2 sketch used when
    the sampled rows of `A` and `b` are scaled by leverage scores computed from
    `U`, not by the row norms of `A` itself. -/
noncomputable def rowSampleLSMatrixWithBasisScale
    {m n d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => A (samples t) j / rowSampleScaleDen s U (samples t)

/-- Row-sampled least-squares right-hand side with the same basis-probability
    scaling as `rowSampleLSMatrixWithBasisScale`. -/
noncomputable def rowSampleLSVectorWithBasisScale
    {m d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → ℝ :=
  fun t => b (samples t) / rowSampleScaleDen s U (samples t)

/-- Floating-point row-sampled least-squares matrix with leverage probabilities
    supplied by a basis matrix `U`.  This is the literal rounded counterpart of
    `rowSampleLSMatrixWithBasisScale`: each sampled entry of `A` is divided by
    the exact scaling denominator using the repository's `fl_div` model. -/
noncomputable def fl_rowSampleLSMatrixWithBasisScale
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => fp.fl_div (A (samples t) j) (rowSampleScaleDen s U (samples t))

/-- Floating-point row-sampled least-squares right-hand side with the same
    basis-probability scaling as `fl_rowSampleLSMatrixWithBasisScale`. -/
noncomputable def fl_rowSampleLSVectorWithBasisScale
    (fp : FPModel) {m d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → ℝ :=
  fun t => fp.fl_div (b (samples t)) (rowSampleScaleDen s U (samples t))

/-- Entrywise forward error for the literal rounded least-squares sketch
    matrix. -/
theorem fl_rowSampleLSMatrixWithBasisScale_error_bound
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |fl_rowSampleLSMatrixWithBasisScale fp s U A samples t j -
      rowSampleLSMatrixWithBasisScale s U A samples t j| ≤
      |rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u := by
  unfold fl_rowSampleLSMatrixWithBasisScale rowSampleLSMatrixWithBasisScale
  exact fl_div_error_bound fp (A (samples t) j)
    (rowSampleScaleDen s U (samples t)) hdenom

/-- Entrywise forward error for the literal rounded least-squares sketch right
    hand side. -/
theorem fl_rowSampleLSVectorWithBasisScale_error_bound
    (fp : FPModel) {m d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (samples : RowTrace m steps) (t : Fin steps)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |fl_rowSampleLSVectorWithBasisScale fp s U b samples t -
      rowSampleLSVectorWithBasisScale s U b samples t| ≤
      |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  unfold fl_rowSampleLSVectorWithBasisScale rowSampleLSVectorWithBasisScale
  exact fl_div_error_bound fp (b (samples t))
    (rowSampleScaleDen s U (samples t)) hdenom

/-- Residual perturbation induced by the literal rounded least-squares row
    divisions for one sampled row.  This is the first implementation-backed
    foundation needed before the rounded sketched objective can replace the
    current explicit rounded-Gram representation hypothesis. -/
theorem fl_rowSampleLSResidualWithBasisScale_error_bound
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) (t : Fin steps)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |lsResidual
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x t -
      lsResidual
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x t| ≤
      (∑ j : Fin n,
        (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
          |x j|) +
        |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  classical
  let Ahat : Fin steps → Fin n → ℝ :=
    rowSampleLSMatrixWithBasisScale s U A samples
  let bhat : Fin steps → ℝ :=
    rowSampleLSVectorWithBasisScale s U b samples
  let Afl : Fin steps → Fin n → ℝ :=
    fl_rowSampleLSMatrixWithBasisScale fp s U A samples
  let bfl : Fin steps → ℝ :=
    fl_rowSampleLSVectorWithBasisScale fp s U b samples
  have hAerr : ∀ j : Fin n,
      |Afl t j - Ahat t j| ≤ |Ahat t j| * fp.u := by
    intro j
    exact
      fl_rowSampleLSMatrixWithBasisScale_error_bound
        fp s U A samples t j hdenom
  have hberr :
      |bfl t - bhat t| ≤ |bhat t| * fp.u :=
    fl_rowSampleLSVectorWithBasisScale_error_bound
      fp s U b samples t hdenom
  have hsumdiff :
      (∑ j : Fin n, Afl t j * x j) -
        (∑ j : Fin n, Ahat t j * x j) =
        ∑ j : Fin n, (Afl t j - Ahat t j) * x j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiff :
      lsResidual Afl bfl x t - lsResidual Ahat bhat x t =
        (∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
          (bfl t - bhat t) := by
    unfold lsResidual rectMatMulVec
    calc
      (∑ j : Fin n, Afl t j * x j) - bfl t -
          ((∑ j : Fin n, Ahat t j * x j) - bhat t)
          =
        ((∑ j : Fin n, Afl t j * x j) -
          (∑ j : Fin n, Ahat t j * x j)) -
          (bfl t - bhat t) := by
            ring
      _ = (∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
            (bfl t - bhat t) := by
            rw [hsumdiff]
  calc
    |lsResidual Afl bfl x t - lsResidual Ahat bhat x t|
        = |(∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
            (bfl t - bhat t)| := by
            rw [hdiff]
    _ ≤ |∑ j : Fin n, (Afl t j - Ahat t j) * x j| +
          |bfl t - bhat t| := by
            simpa [abs_sub_comm] using
              (abs_sub_le (∑ j : Fin n, (Afl t j - Ahat t j) * x j)
                0 (bfl t - bhat t))
    _ ≤ (∑ j : Fin n, |(Afl t j - Ahat t j) * x j|) +
          |bfl t - bhat t| := by
            exact add_le_add
              (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ = (∑ j : Fin n, |Afl t j - Ahat t j| * |x j|) +
          |bfl t - bhat t| := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul (Afl t j - Ahat t j) (x j)
    _ ≤ (∑ j : Fin n, (|Ahat t j| * fp.u) * |x j|) +
          |bhat t| * fp.u := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (hAerr j) (abs_nonneg _)
            · exact hberr

/-- Support-specialized residual perturbation bound for the canonical row-trace
    law: on traces whose sampled basis rows have positive probability, the
    row-scaling denominators are nonzero and the rounded residual bound applies
    without an extra denominator premise. -/
theorem fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ) (t : Fin s)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsResidual
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x t -
      lsResidual
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x t| ≤
      (∑ j : Fin n,
        (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
          |x j|) +
        |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  exact
    fl_rowSampleLSResidualWithBasisScale_error_bound
      fp s A b U samples x t
      (rowSampleScaleDen_ne_zero s U (samples t) hs (hprob t))

/-- Generic deterministic lift from a residual-vector perturbation to a
    squared least-squares objective perturbation. -/
theorem lsObjective_residual_difference_bound
    {m n : ℕ}
    (Aexact Apert : Fin m → Fin n → ℝ)
    (bexact bpert : Fin m → ℝ) (x : Fin n → ℝ) :
    |lsObjective Apert bpert x - lsObjective Aexact bexact x| ≤
      2 * vecNorm2 (lsResidual Aexact bexact x) *
          vecNorm2 (fun i : Fin m =>
            lsResidual Apert bpert x i - lsResidual Aexact bexact x i) +
        vecNorm2Sq (fun i : Fin m =>
          lsResidual Apert bpert x i - lsResidual Aexact bexact x i) := by
  let r : Fin m → ℝ := lsResidual Aexact bexact x
  let e : Fin m → ℝ := fun i =>
    lsResidual Apert bpert x i - lsResidual Aexact bexact x i
  have hres : lsResidual Apert bpert x = fun i : Fin m => r i + e i := by
    ext i
    simp [r, e]
  unfold lsObjective
  rw [hres]
  simpa [r, e] using abs_vecNorm2Sq_add_sub_le r e

/-- Budgeted deterministic lift from entrywise residual perturbations to a
    squared least-squares objective perturbation. -/
theorem lsObjective_residual_budget_bound
    {m n : ℕ}
    (Aexact Apert : Fin m → Fin n → ℝ)
    (bexact bpert : Fin m → ℝ) (x : Fin n → ℝ)
    (budget : Fin m → ℝ)
    (hbudget : ∀ i : Fin m,
      |lsResidual Apert bpert x i - lsResidual Aexact bexact x i| ≤ budget i) :
    |lsObjective Apert bpert x - lsObjective Aexact bexact x| ≤
      2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget +
        vecNorm2Sq budget := by
  let e : Fin m → ℝ := fun i =>
    lsResidual Apert bpert x i - lsResidual Aexact bexact x i
  have hbase :=
    lsObjective_residual_difference_bound Aexact Apert bexact bpert x
  have he_norm : vecNorm2 e ≤ vecNorm2 budget := by
    exact vecNorm2_le_of_abs_le e budget hbudget
  have he_sq : vecNorm2Sq e ≤ vecNorm2Sq budget := by
    exact vecNorm2Sq_le_of_abs_le e budget hbudget
  have hcoef_nonneg :
      0 ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) := by
    exact mul_nonneg (by norm_num) (vecNorm2_nonneg _)
  have hterm :
      2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 e ≤
        2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget := by
    exact mul_le_mul_of_nonneg_left he_norm hcoef_nonneg
  calc
    |lsObjective Apert bpert x - lsObjective Aexact bexact x|
        ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 e +
            vecNorm2Sq e := hbase
    _ ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget +
          vecNorm2Sq budget := by
          exact add_le_add hterm he_sq

/-- Residual budget induced by a componentwise forward-error bound on the
    least-squares solution vector. -/
noncomputable def lsSolutionForwardResidualBudget {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (dx : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, |A i j| * dx j

/-- Objective gap induced by a componentwise forward-error bound on a vector
    near an exact least-squares minimizer. -/
noncomputable def lsSolutionForwardObjectiveGap {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xStar : Fin n → ℝ) (dx : Fin n → ℝ) : ℝ :=
  2 * vecNorm2 (lsResidual A b xStar) *
      vecNorm2 (lsSolutionForwardResidualBudget A dx) +
    vecNorm2Sq (lsSolutionForwardResidualBudget A dx)

/-- A componentwise solution-vector error bound induces a rowwise residual
    perturbation bound. -/
theorem lsResidual_difference_bound_of_solution_abs_le
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (_hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j)
    (i : Fin m) :
    |lsResidual A b xHat i - lsResidual A b xStar i| ≤
      lsSolutionForwardResidualBudget A dx i := by
  have hdiff :
      lsResidual A b xHat i - lsResidual A b xStar i =
        ∑ j : Fin n, A i j * (xHat j - xStar j) := by
    unfold lsResidual rectMatMulVec
    calc
      (∑ j : Fin n, A i j * xHat j) - b i -
          ((∑ j : Fin n, A i j * xStar j) - b i)
          = (∑ j : Fin n, A i j * xHat j) -
              (∑ j : Fin n, A i j * xStar j) := by ring
      _ = ∑ j : Fin n, (A i j * xHat j - A i j * xStar j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin n, A i j * (xHat j - xStar j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
  calc
    |lsResidual A b xHat i - lsResidual A b xStar i|
        = |∑ j : Fin n, A i j * (xHat j - xStar j)| := by
            rw [hdiff]
    _ ≤ ∑ j : Fin n, |A i j * (xHat j - xStar j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |xHat j - xStar j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
    _ ≤ ∑ j : Fin n, |A i j| * dx j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hclose j) (abs_nonneg _)
    _ = lsSolutionForwardResidualBudget A dx i := rfl

/-- Objective perturbation bound induced by a componentwise solution-vector
    forward-error certificate. -/
theorem lsObjective_solution_forward_error_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j) :
    |lsObjective A b xHat - lsObjective A b xStar| ≤
      lsSolutionForwardObjectiveGap A b xStar dx := by
  let e : Fin m → ℝ := fun i =>
    lsResidual A b xHat i - lsResidual A b xStar i
  have hres :
      lsResidual A b xHat =
        fun i : Fin m => lsResidual A b xStar i + e i := by
    ext i
    simp [e]
  have hbase :
      |vecNorm2Sq (fun i : Fin m => lsResidual A b xStar i + e i) -
          vecNorm2Sq (lsResidual A b xStar)| ≤
        2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e +
          vecNorm2Sq e :=
    abs_vecNorm2Sq_add_sub_le (lsResidual A b xStar) e
  have he_budget : ∀ i : Fin m,
      |e i| ≤ lsSolutionForwardResidualBudget A dx i := by
    intro i
    exact
      lsResidual_difference_bound_of_solution_abs_le
        A b xHat xStar dx hdx hclose i
  have he_norm :
      vecNorm2 e ≤ vecNorm2 (lsSolutionForwardResidualBudget A dx) :=
    vecNorm2_le_of_abs_le e (lsSolutionForwardResidualBudget A dx) he_budget
  have he_sq :
      vecNorm2Sq e ≤ vecNorm2Sq (lsSolutionForwardResidualBudget A dx) :=
    vecNorm2Sq_le_of_abs_le e (lsSolutionForwardResidualBudget A dx) he_budget
  have hcoef_nonneg :
      0 ≤ 2 * vecNorm2 (lsResidual A b xStar) := by
    exact mul_nonneg (by norm_num) (vecNorm2_nonneg _)
  have hterm :
      2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e ≤
        2 * vecNorm2 (lsResidual A b xStar) *
          vecNorm2 (lsSolutionForwardResidualBudget A dx) := by
    exact mul_le_mul_of_nonneg_left he_norm hcoef_nonneg
  unfold lsObjective
  calc
    |vecNorm2Sq (lsResidual A b xHat) -
        vecNorm2Sq (lsResidual A b xStar)|
        = |vecNorm2Sq (fun i : Fin m => lsResidual A b xStar i + e i) -
            vecNorm2Sq (lsResidual A b xStar)| := by
            rw [hres]
    _ ≤ 2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e +
          vecNorm2Sq e := hbase
    _ ≤ 2 * vecNorm2 (lsResidual A b xStar) *
            vecNorm2 (lsSolutionForwardResidualBudget A dx) +
          vecNorm2Sq (lsSolutionForwardResidualBudget A dx) := by
          exact add_le_add hterm he_sq

/-- A componentwise forward-error certificate relative to an exact minimizer
    gives an additive-gap approximate minimizer. -/
theorem isLeastSquaresApproxMinimizer_of_solution_abs_le
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (hstar : IsLeastSquaresMinimizer A b xStar)
    (hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j) :
    IsLeastSquaresApproxMinimizer A b xHat
      (lsSolutionForwardObjectiveGap A b xStar dx) := by
  intro y
  have hdiff :=
    lsObjective_solution_forward_error_bound A b xHat xStar dx hdx hclose
  have hupper :
      lsObjective A b xHat ≤
        lsObjective A b xStar +
          lsSolutionForwardObjectiveGap A b xStar dx := by
    have h := (abs_le.mp hdiff).2
    linarith
  have hmin := hstar y
  linarith

/-- Componentwise solution certificate induced by a perturbed normal-equation
    system and the local Gram forward-error theorem. -/
noncomputable def gramForwardSolverDx {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (εG εg : ℝ)
    (xHat : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    ∑ j : Fin n, |ATA_inv i j| *
      (εG * ∑ k : Fin n, |xHat k| + εg)

/-- The Gram-system forward-error certificate is nonnegative when its scalar
    perturbation radii are nonnegative. -/
theorem gramForwardSolverDx_nonneg {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (εG εg : ℝ)
    (xHat : Fin n → ℝ)
    (hεG : 0 ≤ εG) (hεg : 0 ≤ εg) :
    ∀ i : Fin n, 0 ≤ gramForwardSolverDx ATA_inv εG εg xHat i := by
  intro i
  unfold gramForwardSolverDx
  apply Finset.sum_nonneg
  intro j _
  exact
    mul_nonneg (abs_nonneg _) (add_nonneg
      (mul_nonneg hεG (Finset.sum_nonneg fun k _ => abs_nonneg _))
      hεg)

/-- A perturbed normal-equation solve supplies the componentwise certificate
    used by the literal rounded sampled-row solver theorem.

This is a small adapter around the repository's `gram_forward_error_normwise`:
it does not assert that a particular QR or preconditioner produces the
perturbed system; it converts such a proved perturbed-system certificate into
the `solverDx` shape needed by the RandNLA objective transfer. -/
theorem gram_forward_error_certificate_of_perturbed_gram_system {n : ℕ}
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb xStar xHat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA xStar i = ATb i)
    (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ)
    (hPerturbed : ∀ i,
      matMulVec n (fun a b => ATA a b + ΔG a b) xHat i =
        ATb i + Δg i)
    (εG εg : ℝ)
    (hΔG_bound : ∀ i j, |ΔG i j| ≤ εG)
    (hΔg_bound : ∀ i, |Δg i| ≤ εg)
    (hεG : 0 ≤ εG) (hεg : 0 ≤ εg) :
    ∀ i : Fin n,
      |xHat i - xStar i| ≤
        gramForwardSolverDx ATA_inv εG εg xHat i := by
  exact
    gram_forward_error_normwise n ATA ATA_inv hInv ATb xStar xHat
      hExact ΔG Δg hPerturbed hΔG_bound hΔg_bound hεG hεg

/-- Componentwise solver certificate induced by the local
    `LSQRSolveBackwardError` structure.  The Frobenius bound on `ΔG` is
    converted entrywise using `abs_entry_le_frobNorm`; the right-hand-side
    radius is defensively replaced by `max c_g 0`, so no separate
    nonnegativity hypothesis on `c_g` is needed. -/
noncomputable def lsQRSolveBackwardSolverDx {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (c_G c_g : ℝ)
    (xHat : Fin n → ℝ) : Fin n → ℝ :=
  gramForwardSolverDx ATA_inv c_G (max c_g 0) xHat

/-- The solver certificate extracted from `LSQRSolveBackwardError` is
    nonnegative. -/
theorem lsQRSolveBackwardSolverDx_nonneg {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (c_G c_g : ℝ)
    (xHat : Fin n → ℝ) (hcG : 0 ≤ c_G) :
    ∀ i : Fin n, 0 ≤ lsQRSolveBackwardSolverDx ATA_inv c_G c_g xHat i := by
  intro i
  unfold lsQRSolveBackwardSolverDx
  exact
    gramForwardSolverDx_nonneg ATA_inv c_G (max c_g 0) xHat
      hcG (le_max_right c_g 0) i

/-- A local QR least-squares backward-error specification supplies the
    componentwise forward-error certificate used by the RandNLA objective
    transfer.  This is still a spec adapter: it does not prove that a concrete
    QR implementation establishes `LSQRSolveBackwardError`. -/
theorem gram_forward_error_certificate_of_ls_qr_solve_backward_error {n : ℕ}
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb xStar xHat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA xStar i = ATb i)
    (c_G c_g : ℝ)
    (hBack : LSQRSolveBackwardError n ATA ATb xHat c_G c_g) :
    ∀ i : Fin n,
      |xHat i - xStar i| ≤
        lsQRSolveBackwardSolverDx ATA_inv c_G c_g xHat i := by
  rcases hBack.result with ⟨ΔG, Δg, hPerturbed, hΔG_frob, hΔg_bound⟩
  have hcG : 0 ≤ c_G := le_trans (frobNorm_nonneg ΔG) hΔG_frob
  unfold lsQRSolveBackwardSolverDx
  exact
    gram_forward_error_certificate_of_perturbed_gram_system
      ATA ATA_inv hInv ATb xStar xHat hExact ΔG Δg hPerturbed
      c_G (max c_g 0)
      (fun i j => le_trans (abs_entry_le_frobNorm ΔG i j) hΔG_frob)
      (fun i => le_trans (hΔg_bound i) (le_max_left c_g 0))
      hcG (le_max_right c_g 0)

/-- Entrywise budget for the literal rounded sampled/scaled least-squares
    residual. -/
noncomputable def rowSampleLSResidualFpBudget
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) : Fin steps → ℝ :=
  fun t =>
    (∑ j : Fin n,
      (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
        |x j|) +
      |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u

/-- The rounded sampled residual budget is entrywise nonnegative. -/
theorem rowSampleLSResidualFpBudget_nonneg
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) :
    ∀ t : Fin steps,
      0 ≤ rowSampleLSResidualFpBudget fp s A b U samples x t := by
  intro t
  unfold rowSampleLSResidualFpBudget
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _) fp.u_nonneg)
      (abs_nonneg _)
  · exact mul_nonneg (abs_nonneg _) fp.u_nonneg

/-- Objective-level budget induced by the literal rounded sampled/scaled
    least-squares residual budget. -/
noncomputable def rowSampleLSObjectiveFpBudget
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) : ℝ :=
  2 *
      vecNorm2
        (lsResidual
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples) x) *
      vecNorm2 (rowSampleLSResidualFpBudget fp s A b U samples x) +
    vecNorm2Sq (rowSampleLSResidualFpBudget fp s A b U samples x)

/-- The literal rounded sampled least-squares objective budget is
    nonnegative. -/
theorem rowSampleLSObjectiveFpBudget_nonneg
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) :
    0 ≤ rowSampleLSObjectiveFpBudget fp s A b U samples x := by
  unfold rowSampleLSObjectiveFpBudget
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (vecNorm2_nonneg
          (lsResidual
            (rowSampleLSMatrixWithBasisScale s U A samples)
            (rowSampleLSVectorWithBasisScale s U b samples) x)))
      (vecNorm2_nonneg
        (rowSampleLSResidualFpBudget fp s A b U samples x))
  · exact vecNorm2Sq_nonneg _

/-- Objective-level perturbation bound for the literal rounded sampled/scaled
    least-squares construction on the positive-probability support event.  This
    is the deterministic objective lift of the rowwise residual perturbation;
    a later theorem can combine it with the exact high-probability
    finite-Loewner LS event under an explicit objective budget. -/
theorem fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsObjective
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x -
      lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x| ≤
      2 *
          vecNorm2
            (lsResidual
              (rowSampleLSMatrixWithBasisScale s U A samples)
              (rowSampleLSVectorWithBasisScale s U b samples) x) *
          vecNorm2 (rowSampleLSResidualFpBudget fp s A b U samples x) +
        vecNorm2Sq (rowSampleLSResidualFpBudget fp s A b U samples x) := by
  apply
    lsObjective_residual_budget_bound
      (rowSampleLSMatrixWithBasisScale s U A samples)
      (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (rowSampleLSVectorWithBasisScale s U b samples)
      (fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      x
      (rowSampleLSResidualFpBudget fp s A b U samples x)
  · intro t
    unfold rowSampleLSResidualFpBudget
    exact
      fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb
        fp A b U samples x t hs hprob

/-- Named-budget form of
    `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb`. -/
theorem fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsObjective
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x -
      lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x| ≤
      rowSampleLSObjectiveFpBudget fp s A b U samples x := by
  simpa [rowSampleLSObjectiveFpBudget] using
    fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb
      fp A b U samples x hs hprob

/-- Residual coordinates in an orthonormal-column basis `U`.

For a residual vector `r = A x - b`, this is the coefficient vector `Uᵀ r`.
When `r` lies in the column span of `U`, orthonormality gives
`r = U (Uᵀ r)`. -/
noncomputable def residualCoordinates {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun a => ∑ i : Fin m, U i a * lsResidual A b x i

/-- Every least-squares residual lies in the column span of `U`, expressed via
    the canonical orthonormal-basis coordinates `Uᵀ(Ax-b)`. -/
def ResidualsInColumnSpace {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ∀ i : Fin m,
    lsResidual A b x i =
      ∑ a : Fin d, U i a * residualCoordinates A b U x a

/-- A supplied coordinate representation of the data columns and the right-hand
    side in the columns of `U`. -/
def ColumnsAndRhsInColumnSpace {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ) : Prop :=
  (∀ i : Fin m, ∀ j : Fin n,
    A i j = ∑ a : Fin d, U i a * Acoord j a) ∧
  (∀ i : Fin m, b i = ∑ a : Fin d, U i a * bcoord a)

/-- Residual coordinates induced by coordinate representations of the columns
    of `A` and the vector `b`. -/
noncomputable def residualCoordinatesFromColumns {n d : ℕ}
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (x : Fin n → ℝ) : Fin d → ℝ :=
  fun a => ∑ j : Fin n, Acoord j a * x j - bcoord a

/-- If a residual has any coordinates in an orthonormal-column basis, then the
    canonical coordinates `Uᵀr` reconstruct the same residual. -/
theorem residualsInColumnSpace_of_residual_representation
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a) :
    ResidualsInColumnSpace A b U := by
  have hcoord :
      ∀ x : Fin n → ℝ, residualCoordinates A b U x = coord x := by
    intro x
    ext a
    unfold residualCoordinates
    simp_rw [hres x]
    calc
      ∑ i : Fin m, U i a * (∑ c : Fin d, U i c * coord x c)
          = ∑ c : Fin d, (∑ i : Fin m, U i a * U i c) * coord x c := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro c _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ c : Fin d, (if a = c then 1 else 0) * coord x c := by
              apply Finset.sum_congr rfl
              intro c _
              rw [hU a c]
      _ = coord x a := by
              simp [Finset.mem_univ]
  intro x i
  rw [hcoord x]
  exact hres x i

/-- Column-coordinate representations for `A` and `b` induce a residual
    coordinate representation for every `A x - b`. -/
theorem lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (hcols : ColumnsAndRhsInColumnSpace A b U Acoord bcoord)
    (x : Fin n → ℝ) (i : Fin m) :
    lsResidual A b x i =
      ∑ a : Fin d, U i a *
        residualCoordinatesFromColumns Acoord bcoord x a := by
  have hA := hcols.1
  have hb := hcols.2
  unfold lsResidual rectMatMulVec residualCoordinatesFromColumns
  calc
    ∑ j : Fin n, A i j * x j - b i
        = ∑ j : Fin n, (∑ a : Fin d, U i a * Acoord j a) * x j -
            ∑ a : Fin d, U i a * bcoord a := by
            rw [hb i]
            apply congrArg₂ Sub.sub
            · apply Finset.sum_congr rfl
              intro j _
              rw [hA i j]
            · rfl
    _ = ∑ a : Fin d, U i a *
          (∑ j : Fin n, Acoord j a * x j - bcoord a) := by
            calc
              ∑ j : Fin n, (∑ a : Fin d, U i a * Acoord j a) * x j -
                  ∑ a : Fin d, U i a * bcoord a
                  =
                (∑ a : Fin d, U i a *
                  ∑ j : Fin n, Acoord j a * x j) -
                  ∑ a : Fin d, U i a * bcoord a := by
                    apply congrArg₂ Sub.sub
                    · simp_rw [Finset.sum_mul]
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
                    · rfl
              _ = ∑ a : Fin d, U i a *
                    (∑ j : Fin n, Acoord j a * x j - bcoord a) := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring

/-- If the columns of `A` and the right-hand side `b` lie in an
    orthonormal-column basis `U`, then every least-squares residual lies in the
    column span of `U`. -/
theorem residualsInColumnSpace_of_columnsAndRhsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (hcols : ColumnsAndRhsInColumnSpace A b U Acoord bcoord) :
    ResidualsInColumnSpace A b U := by
  exact
    residualsInColumnSpace_of_residual_representation
      A b U hU (residualCoordinatesFromColumns Acoord bcoord)
      (fun x i =>
        lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace
          A b U Acoord bcoord hcols x i)

/-- Embed a finite real coordinate vector into Mathlib's Euclidean-space type.

The RandNLA files use plain functions `Fin m → ℝ` for matrices and vectors,
while Mathlib's orthonormal-basis API uses `EuclideanSpace ℝ (Fin m)`.  This
small bridge lets us reuse Mathlib's finite-dimensional orthonormal-basis
construction without changing the algorithm-facing definitions. -/
noncomputable def euclideanVec {m : ℕ} (v : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 v

@[simp]
theorem euclideanVec_apply {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    euclideanVec v i = v i := rfl

/-- The augmented least-squares data vectors: all columns of `A` and the
right-hand side `b`, viewed as vectors in `ℝ^m`. -/
noncomputable def augmentedDataVector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Sum (Fin n) Unit → EuclideanSpace ℝ (Fin m)
  | Sum.inl j => euclideanVec (fun i => A i j)
  | Sum.inr _ => euclideanVec b

/-- The finite-dimensional augmented data span `span{columns(A), b}`. -/
noncomputable def augmentedDataSpan {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range (augmentedDataVector A b))

/-- Every augmented data vector belongs to the augmented data span. -/
theorem augmentedDataVector_mem_span {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (c : Sum (Fin n) Unit) :
    augmentedDataVector A b c ∈ augmentedDataSpan A b := by
  exact Submodule.subset_span (Set.mem_range_self c)

/-- The orthonormal-column matrix obtained by choosing Mathlib's standard
orthonormal basis of the augmented data span.  Its number of columns is the
rank/dimension of `span{columns(A), b}`. -/
noncomputable def augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin m → Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun i a =>
    (((stdOrthonormalBasis ℝ (augmentedDataSpan A b) a :
      augmentedDataSpan A b) : EuclideanSpace ℝ (Fin m)) i)

/-- Coordinates of the columns of `A` in the augmented-span orthonormal basis. -/
noncomputable def augmentedSpanColumnCoords {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun j a =>
    (stdOrthonormalBasis ℝ (augmentedDataSpan A b)).repr
      ⟨augmentedDataVector A b (Sum.inl j),
        augmentedDataVector_mem_span A b (Sum.inl j)⟩ a

/-- Coordinates of `b` in the augmented-span orthonormal basis. -/
noncomputable def augmentedSpanRhsCoords {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun a =>
    (stdOrthonormalBasis ℝ (augmentedDataSpan A b)).repr
      ⟨augmentedDataVector A b (Sum.inr ()),
        augmentedDataVector_mem_span A b (Sum.inr ())⟩ a

/-- The augmented-span basis matrix has orthonormal columns. -/
theorem hasOrthonormalColumns_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    HasOrthonormalColumns (augmentedSpanBasisMatrix A b) := by
  intro j k
  let S := augmentedDataSpan A b
  let B := stdOrthonormalBasis ℝ S
  have h := B.inner_eq_ite j k
  rw [Submodule.coe_inner, PiLp.inner_apply] at h
  calc
    ∑ i : Fin m,
        augmentedSpanBasisMatrix A b i j *
          augmentedSpanBasisMatrix A b i k
        = ∑ i : Fin m,
            inner ℝ
              (((B j : S) : EuclideanSpace ℝ (Fin m)) i)
              (((B k : S) : EuclideanSpace ℝ (Fin m)) i) := by
            apply Finset.sum_congr rfl
            intro i _
            change
              augmentedSpanBasisMatrix A b i j *
                  augmentedSpanBasisMatrix A b i k =
                RCLike.re
                  ((((B k : S) : EuclideanSpace ℝ (Fin m)) i) *
                    (starRingEnd ℝ)
                      (((B j : S) : EuclideanSpace ℝ (Fin m)) i))
            simp [augmentedSpanBasisMatrix, S, B, mul_comm]
    _ = if j = k then (1 : ℝ) else 0 := h

/-- The augmented-span orthonormal basis represents every column of `A` and the
right-hand side `b`. -/
theorem columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ColumnsAndRhsInColumnSpace A b
      (augmentedSpanBasisMatrix A b)
      (augmentedSpanColumnCoords A b)
      (augmentedSpanRhsCoords A b) := by
  constructor
  · intro i j
    let S := augmentedDataSpan A b
    let B := stdOrthonormalBasis ℝ S
    let x : S :=
      ⟨augmentedDataVector A b (Sum.inl j),
        augmentedDataVector_mem_span A b (Sum.inl j)⟩
    have hsum := B.sum_repr x
    have hi :=
      congrArg (fun v : S => ((v : EuclideanSpace ℝ (Fin m)) i)) hsum
    symm
    simpa [augmentedSpanBasisMatrix, augmentedSpanColumnCoords,
      augmentedDataVector, euclideanVec, S, B, x, Pi.smul_apply,
      smul_eq_mul, mul_comm] using hi
  · intro i
    let S := augmentedDataSpan A b
    let B := stdOrthonormalBasis ℝ S
    let x : S :=
      ⟨augmentedDataVector A b (Sum.inr ()),
        augmentedDataVector_mem_span A b (Sum.inr ())⟩
    have hsum := B.sum_repr x
    have hi :=
      congrArg (fun v : S => ((v : EuclideanSpace ℝ (Fin m)) i)) hsum
    symm
    simpa [augmentedSpanBasisMatrix, augmentedSpanRhsCoords,
      augmentedDataVector, euclideanVec, S, B, x, Pi.smul_apply,
      smul_eq_mul, mul_comm] using hi

/-- Every least-squares residual lies in the augmented data span basis. -/
theorem residualsInColumnSpace_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ResidualsInColumnSpace A b (augmentedSpanBasisMatrix A b) := by
  exact
    residualsInColumnSpace_of_columnsAndRhsInColumnSpace
      A b (augmentedSpanBasisMatrix A b)
      (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
      (augmentedSpanColumnCoords A b)
      (augmentedSpanRhsCoords A b)
      (columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix A b)

/-- The square identity matrix has orthonormal columns. -/
theorem hasOrthonormalColumns_idMatrix (m : ℕ) :
    HasOrthonormalColumns (idMatrix m) := by
  intro j k
  unfold idMatrix
  by_cases hjk : j = k
  · subst k
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  · calc
      (∑ i : Fin m, (if i = j then (1 : ℝ) else 0) *
          (if i = k then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hij : i = j
        · simp [hij, hjk]
        · simp [hij]
      _ = (if j = k then (1 : ℝ) else 0) := by
        simp [hjk]

/-- Canonical residual coordinates in the full identity basis are just the
    residual vector itself. -/
theorem residualCoordinates_idMatrix
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    residualCoordinates A b (idMatrix m) x = lsResidual A b x := by
  ext a
  simp [residualCoordinates, idMatrix, eq_comm]

/-- The identity basis contains every least-squares residual.  This is the
    full-row-space fallback basis for equation (6): it is not the sharp
    low-dimensional leverage basis, but it discharges the column-space
    hypothesis without any SVD/QR infrastructure. -/
theorem residualsInColumnSpace_idMatrix
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ResidualsInColumnSpace A b (idMatrix m) := by
  intro x i
  have hid := congrFun (idMatrix_mulVec m (lsResidual A b x)) i
  rw [residualCoordinates_idMatrix A b x]
  exact hid.symm

/-- If all residuals lie in the column span of an orthonormal-column matrix
    `U`, then the original least-squares objective is exactly the squared norm
    of the canonical residual-coordinate vector. -/
theorem lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hcol : ResidualsInColumnSpace A b U)
    (x : Fin n → ℝ) :
    lsObjective A b x = vecNorm2Sq (residualCoordinates A b U x) := by
  let c : Fin d → ℝ := residualCoordinates A b U x
  have hres :
      lsResidual A b x =
        fun i : Fin m => ∑ a : Fin d, U i a * c a := by
    ext i
    exact hcol x i
  have hgram : rowSketchGram U = idMatrix d := by
    ext j k
    exact hU j k
  calc
    lsObjective A b x = vecNorm2Sq (lsResidual A b x) := rfl
    _ = vecNorm2Sq
        (fun i : Fin m => ∑ a : Fin d, U i a * c a) := by
          rw [hres]
    _ = ∑ a : Fin d, c a * matMulVec d (rowSketchGram U) c a := by
          exact
            vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
              U c
    _ = ∑ a : Fin d, c a * matMulVec d (idMatrix d) c a := by
          rw [hgram]
    _ = vecNorm2Sq c := quadraticForm_idMatrix_eq_vecNorm2Sq c

/-- The concrete sampled least-squares residual is the sampled/scaled
    coordinate residual whenever the original residual is represented in the
    rows of `U`.

This closes the row-sampling algebra part of equation (8); existence of such a
coordinate representation for a chosen augmented residual basis is a separate
rank/SVD or QR foundation. -/
theorem rowSampleLSResidualWithBasisScale_eq_coord
    {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a)
    (x : Fin n → ℝ) (t : Fin steps) :
    lsResidual
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x t =
      ∑ a : Fin d, rowSampleSketch s U samples t a * coord x a := by
  unfold lsResidual rectMatMulVec rowSampleLSMatrixWithBasisScale
    rowSampleLSVectorWithBasisScale rowSampleSketch rowSampleIncrement
  simp_rw [div_eq_mul_inv]
  let denomInv : ℝ := (rowSampleScaleDen s U (samples t))⁻¹
  have hres_expanded :
      ∑ j : Fin n, A (samples t) j * x j - b (samples t) =
        ∑ a : Fin d, U (samples t) a * coord x a := by
    simpa [lsResidual, rectMatMulVec] using hres x (samples t)
  calc
    ∑ j : Fin n, A (samples t) j * denomInv * x j -
        b (samples t) * denomInv
        = (∑ j : Fin n, A (samples t) j * x j - b (samples t)) *
            denomInv := by
            rw [sub_mul, Finset.sum_mul]
            apply congrArg₂ Sub.sub
            · apply Finset.sum_congr rfl
              intro j _
              ring
            · ring
    _ = (∑ a : Fin d, U (samples t) a * coord x a) * denomInv := by
            rw [hres_expanded]
    _ = ∑ a : Fin d, U (samples t) a * denomInv * coord x a := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            ring

/-- Concrete objective representation for a row-sampled least-squares sketch
    scaled by leverage probabilities from a basis matrix `U`.

If every original residual has coordinates `coord x` in the rows of `U`, then
the sampled objective is exactly the coordinate norm plus the quadratic form of
the sampled Gram error `ŨᵀŨ - I`.  This is the missing algebraic link between
the Algorithm 2 equation (7) Gram event and the equation (8) least-squares
objective bridge. -/
theorem rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
    {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a)
    (x : Fin n → ℝ) :
    lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x =
      vecNorm2Sq (coord x) +
        ∑ j : Fin d, coord x j *
          matMulVec d
            (fun j k => rowSampleGram s U samples j k - idMatrix d j k)
            (coord x) j := by
  let y : Fin d → ℝ := coord x
  have hresidual :
      lsResidual
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples) x =
        fun t : Fin steps =>
          ∑ a : Fin d, rowSampleSketch s U samples t a * y a := by
    ext t
    exact rowSampleLSResidualWithBasisScale_eq_coord
      s A b U samples coord hres x t
  calc
    lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x
        = vecNorm2Sq
            (fun t : Fin steps =>
              ∑ a : Fin d, rowSampleSketch s U samples t a * y a) := by
            unfold lsObjective
            rw [hresidual]
    _ = ∑ j : Fin d, y j * matMulVec d (rowSampleGram s U samples) y j := by
            exact
              vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram
                s U samples y
    _ = vecNorm2Sq y +
        ∑ j : Fin d, y j *
          matMulVec d
            (fun j k => rowSampleGram s U samples j k - idMatrix d j k) y j := by
            rw [← vecNorm2Sq_add_quadraticForm_sub_id_eq_quadraticForm
              (rowSampleGram s U samples) y]

/-- A coordinate-space quadratic-form error implies residual-objective
    preservation.

This is the deterministic algebraic bridge used by subspace-embedding
arguments.  The map `coord` represents each original residual in an
orthonormal coordinate system, so `horig` states that the original objective is
`||coord x||₂²`.  The sketched objective is allowed to differ by the quadratic
form `coord(x)ᵀ E coord(x)`.  If `E` has operator-2 norm at most `ε`, then the
sketch preserves every squared residual objective within `1 ± ε`.

The theorem does not prove that a random sketch produces such an `E`; it is the
deterministic bridge that a later randomized subspace-embedding theorem can
compose with. -/
theorem preservesLSObjective_of_coordinate_quadratic_error
    {m n r d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Fin d → Fin d → ℝ) {ε : ℝ}
    (_hε_nonneg : 0 ≤ ε)
    (hE : opNorm2Le E ε)
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ x : Fin n → ℝ,
      lsObjective SA Sb x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d E (coord x) j) :
    PreservesLSObjective A b SA Sb ε := by
  intro x
  let y : Fin d → ℝ := coord x
  have hquad_abs :
      |∑ j : Fin d, y j * matMulVec d E y j| ≤ ε * vecNorm2Sq y :=
    abs_vecInnerProduct_matMulVec_le_of_opNorm2Le E hE y
  have hquad_lower :
      -(ε * vecNorm2Sq y) ≤
        ∑ j : Fin d, y j * matMulVec d E y j :=
    (abs_le.mp hquad_abs).1
  have hquad_upper :
      ∑ j : Fin d, y j * matMulVec d E y j ≤ ε * vecNorm2Sq y :=
    (abs_le.mp hquad_abs).2
  have hnorm_nonneg : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  constructor
  · rw [horig x, hsketch x]
    change (1 - ε) * vecNorm2Sq y ≤
      vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j
    nlinarith
  · rw [horig x, hsketch x]
    change vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j ≤
      (1 + ε) * vecNorm2Sq y
    nlinarith

/-- High-probability transfer version of
    `preservesLSObjective_of_coordinate_quadratic_error`.

If a probability theorem already proves that the random coordinate-space Gram
error `E ω` has operator-2 norm at most `ε`, and each outcome has the stated
coordinate/quadratic representation, then the same probability lower bound
holds for the least-squares preservation event.  This theorem is deliberately
only a transfer: the probability bound `hprob` must come from a separately
proved concentration result. -/
theorem eventProb_preservesLSObjective_of_coordinate_quadratic_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ) {ε α : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hprob : α ≤ P.eventProb {ω | opNorm2Le (E ω) ε})
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
  have hsubset :
      {ω | opNorm2Le (E ω) ε} ⊆
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
    intro ω hE
    exact preservesLSObjective_of_coordinate_quadratic_error
      A b (SA ω) (Sb ω) coord (E ω) hε_nonneg hE horig
      (hsketch ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- A coordinate-space two-sided finite-Loewner event implies residual-objective
    preservation.

This is the sharper analogue of
`preservesLSObjective_of_coordinate_quadratic_error`: instead of first
converting to an operator-norm bound, it consumes the exact two-sided Loewner
event produced by the Bennett route for leverage-score row sampling. -/
theorem preservesLSObjective_of_coordinate_finiteLoewner_error
    {m n r d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Fin d → Fin d → ℝ) {ε : ℝ}
    (hUpper :
      finiteLoewnerLe E
        (fun j k : Fin d => ε * finiteIdMatrix j k))
    (hLower :
      finiteLoewnerLe (fun j k : Fin d => -E j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ x : Fin n → ℝ,
      lsObjective SA Sb x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d E (coord x) j) :
    PreservesLSObjective A b SA Sb ε := by
  intro x
  let y : Fin d → ℝ := coord x
  have hquad_abs :
      |∑ j : Fin d, y j * matMulVec d E y j| ≤ ε * vecNorm2Sq y := by
    have hfinite :=
      abs_finiteQuadraticForm_le_of_loewnerLe_neg
        E hUpper hLower y
    simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
      finiteVecNorm2Sq_fin] using hfinite
  have hquad_lower :
      -(ε * vecNorm2Sq y) ≤
        ∑ j : Fin d, y j * matMulVec d E y j :=
    (abs_le.mp hquad_abs).1
  have hquad_upper :
      ∑ j : Fin d, y j * matMulVec d E y j ≤ ε * vecNorm2Sq y :=
    (abs_le.mp hquad_abs).2
  have hnorm_nonneg : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  constructor
  · rw [horig x, hsketch x]
    change (1 - ε) * vecNorm2Sq y ≤
      vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j
    nlinarith
  · rw [horig x, hsketch x]
    change vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j ≤
      (1 + ε) * vecNorm2Sq y
    nlinarith

/-- Probability transfer for the coordinate-space finite-Loewner bridge. -/
theorem eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ) {ε α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)})
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
  have hsubset :
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)} ⊆
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
    intro ω hE
    exact preservesLSObjective_of_coordinate_finiteLoewner_error
      A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
      (hsketch ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Least-squares objectives are nonnegative. -/
theorem lsObjective_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    0 ≤ lsObjective A b x := by
  unfold lsObjective
  exact vecNorm2Sq_nonneg _

/-- Deterministic equation (8) sketching consequence, squared-objective form.

If a sketch preserves all squared residual objectives by `1 ± ε` and `x_hat`
minimizes the sketched problem, then for every comparison vector `x_ref`,

`||A x_hat - b||₂² ≤ ((1 + ε) / (1 - ε)) ||A x_ref - b||₂²`.

The randomized theorem that a particular Algorithm 2 sketch satisfies
`PreservesLSObjective` with high probability is not assumed here and is not
proved by this theorem. -/
theorem lsObjective_le_of_sketch_preserves
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SA Sb x_hat) :
    lsObjective A b x_hat ≤
      ((1 + ε) / (1 - ε)) * lsObjective A b x_ref := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hmin := hhat x_ref
  have hupper := (hpres x_ref).2
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref :=
    le_trans hlower (le_trans hmin hupper)
  have hdiv :
      lsObjective A b x_hat ≤
        ((1 + ε) * lsObjective A b x_ref) / (1 - ε) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  have hrewrite :
      ((1 + ε) * lsObjective A b x_ref) / (1 - ε) =
        ((1 + ε) / (1 - ε)) * lsObjective A b x_ref := by
    ring
  simpa [hrewrite] using hdiv

/-- Deterministic equation (8) sketching consequence with the common
    `1 + η` target factor.

It is enough to prove
`(1 + ε) / (1 - ε) ≤ 1 + η` for the chosen embedding accuracy `ε`; this theorem
keeps that arithmetic choice explicit. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η : ℝ}
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SA Sb x_hat) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hmain :=
    lsObjective_le_of_sketch_preserves A b SA Sb x_hat x_opt hε hpres hhat
  have hobj : 0 ≤ lsObjective A b x_opt := lsObjective_nonneg A b x_opt
  exact le_trans hmain (mul_le_mul_of_nonneg_right hfactor hobj)

/-- Deterministic transfer from an exact sketched objective to a rounded
    sketched objective with explicit additive objective-error budgets.

If `SA,Sb` preserve the original objective, `SAr,Sbr` are the rounded sketch,
and `x_hat` minimizes the rounded sketch, then the original objective at
`x_hat` is bounded by the exact-sketch factor plus the two objective
perturbation budgets: one at `x_hat` and one at the comparison vector. -/
theorem lsObjective_le_of_sketch_preserves_with_objective_error
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε τHat τRef : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SAr Sbr x_hat)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseRef :
      |lsObjective SAr Sbr x_ref - lsObjective SA Sb x_ref| ≤ τRef) :
    lsObjective A b x_hat ≤
      (((1 + ε) * lsObjective A b x_ref + τHat + τRef) /
        (1 - ε)) := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hupper := (hpres x_ref).2
  have hmin := hhat x_ref
  have hcloseHat' :
      lsObjective SA Sb x_hat ≤ lsObjective SAr Sbr x_hat + τHat := by
    have h := (abs_le.mp hcloseHat).1
    linarith
  have hcloseRef' :
      lsObjective SAr Sbr x_ref ≤ lsObjective SA Sb x_ref + τRef := by
    have h := (abs_le.mp hcloseRef).2
    linarith
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref + τHat + τRef := by
    calc
      (1 - ε) * lsObjective A b x_hat
          ≤ lsObjective SA Sb x_hat := hlower
      _ ≤ lsObjective SAr Sbr x_hat + τHat := hcloseHat'
      _ ≤ lsObjective SAr Sbr x_ref + τHat := by
            linarith
      _ ≤ lsObjective SA Sb x_ref + τRef + τHat := by
            linarith
      _ ≤ (1 + ε) * lsObjective A b x_ref + τRef + τHat := by
            linarith
      _ = (1 + ε) * lsObjective A b x_ref + τHat + τRef := by
            ring
  rw [le_div_iff₀ hpos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain

/-- `1 + η` form of
    `lsObjective_le_of_sketch_preserves_with_objective_error`.

The additive rounded-objective budgets must be small enough to fit inside the
slack between the exact sketch factor and the requested final factor.  The
hypothesis is explicit so this theorem cannot hide an unproved concentration or
perturbation estimate. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η τHat τOpt : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SAr Sbr x_hat)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseOpt :
      |lsObjective SAr Sbr x_opt - lsObjective SA Sb x_opt| ≤ τOpt)
    (hbudget :
      τHat + τOpt ≤
        ((1 + η) * (1 - ε) - (1 + ε)) * lsObjective A b x_opt) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hpos : 0 < 1 - ε := by linarith
  have hmain :=
    lsObjective_le_of_sketch_preserves_with_objective_error
      A b SA SAr Sb Sbr x_hat x_opt hε hpres hhat hcloseHat hcloseOpt
  refine le_trans hmain ?_
  rw [div_le_iff₀ hpos]
  nlinarith [hbudget]

/-- Deterministic transfer from an exact sketched objective to a rounded
    sketched objective with explicit additive objective-error budgets and an
    explicit solver objective gap.

This is the solver-facing version of
`lsObjective_le_of_sketch_preserves_with_objective_error`: instead of requiring
`x_hat` to be an exact minimizer of the rounded sketch, it only requires an
additive-gap approximate minimizer. -/
theorem lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε τHat τRef solverGap : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresApproxMinimizer SAr Sbr x_hat solverGap)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseRef :
      |lsObjective SAr Sbr x_ref - lsObjective SA Sb x_ref| ≤ τRef) :
    lsObjective A b x_hat ≤
      (((1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap) /
        (1 - ε)) := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hupper := (hpres x_ref).2
  have hmin := hhat x_ref
  have hcloseHat' :
      lsObjective SA Sb x_hat ≤ lsObjective SAr Sbr x_hat + τHat := by
    have h := (abs_le.mp hcloseHat).1
    linarith
  have hcloseRef' :
      lsObjective SAr Sbr x_ref ≤ lsObjective SA Sb x_ref + τRef := by
    have h := (abs_le.mp hcloseRef).2
    linarith
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap := by
    calc
      (1 - ε) * lsObjective A b x_hat
          ≤ lsObjective SA Sb x_hat := hlower
      _ ≤ lsObjective SAr Sbr x_hat + τHat := hcloseHat'
      _ ≤ lsObjective SAr Sbr x_ref + solverGap + τHat := by
            linarith
      _ ≤ lsObjective SA Sb x_ref + τRef + solverGap + τHat := by
            linarith
      _ ≤ (1 + ε) * lsObjective A b x_ref + τRef + solverGap + τHat := by
            linarith
      _ = (1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap := by
            ring
  rw [le_div_iff₀ hpos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain

/-- `1 + η` form of the rounded-objective transfer with an explicit additive
    solver objective gap.

The floating-point objective budgets and solver gap must jointly fit inside the
same slack.  This theorem is deterministic; no concentration or solver accuracy
claim is assumed implicitly. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η τHat τOpt solverGap : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresApproxMinimizer SAr Sbr x_hat solverGap)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseOpt :
      |lsObjective SAr Sbr x_opt - lsObjective SA Sb x_opt| ≤ τOpt)
    (hbudget :
      τHat + τOpt + solverGap ≤
        ((1 + η) * (1 - ε) - (1 + ε)) * lsObjective A b x_opt) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hpos : 0 < 1 - ε := by linarith
  have hmain :=
    lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap
      A b SA SAr Sb Sbr x_hat x_opt hε hpres hhat hcloseHat hcloseOpt
  refine le_trans hmain ?_
  rw [div_le_iff₀ hpos]
  nlinarith [hbudget]

/-- Probability transfer from least-squares preservation to the randomized
    sketched-minimizer objective guarantee. -/
theorem eventProb_lsObjective_le_of_preserves
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xRef : Fin n → ℝ)
    {ε α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω)) :
    α ≤ P.eventProb
      {ω |
        lsObjective A b (xHat ω) ≤
          ((1 + ε) / (1 - ε)) * lsObjective A b xRef} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω |
          lsObjective A b (xHat ω) ≤
            ((1 + ε) / (1 - ε)) * lsObjective A b xRef} := by
    intro ω hpres
    exact lsObjective_le_of_sketch_preserves
      A b (SA ω) (Sb ω) (xHat ω) xRef hε hpres (hhat ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer from least-squares preservation to the common
    `1 + η` randomized sketched-minimizer objective guarantee. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω)) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hpres
    exact lsObjective_le_one_add_eta_of_sketch_preserves
      A b (SA ω) (Sb ω) (xHat ω) xOpt hε hfactor hpres (hhat ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched least-squares minimizers with
    explicit additive objective-error budgets.

The event must contain both the exact sketch-preservation property and the
budget inequality that absorbs the rounded-objective errors at the computed
minimizer and at `xOpt`.  This theorem is a composition rule only: it does not
prove the budget event. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hω.1 (hhat ω) (hcloseHat ω) (hcloseOpt ω) hω.2
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched minimizers when the rounded
    objective-error budget inequality is deterministic for every outcome.

This is the form used when the exact sketch-preservation event already has a
proved high-probability bound and the floating-point budget is supplied
pointwise. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_pointwise_objective_error
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hbudget : ∀ ω,
      τHat ω + τOpt ω ≤
        ((1 + η) * (1 - ε) - (1 + ε)) *
          lsObjective A b xOpt)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hpres
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω) (hcloseOpt ω) (hbudget ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched minimizers when the rounded
    objective-error bounds are only available on an auxiliary good event.

This is the support-aware version needed by literal row sampling: division
error bounds require the sampled row to have positive leverage probability, and
that condition is carried as the explicit event `Good`. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_on_event
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hpres, hbudget⟩
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched approximate minimizers when the
    rounded objective-error bounds are only available on an auxiliary good
    event and a solver objective gap is explicit. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_and_solver_gap_on_event
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt solverGap : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω,
      IsLeastSquaresApproxMinimizer (SAr ω) (Sbr ω) (xHat ω)
        (solverGap ω))
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hpres, hbudget⟩
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Finite-Loewner exact sketch preservation plus explicit rounded-objective
    budgets gives a high-probability rounded-minimizer objective bound.

The event carries the auxiliary good condition needed for floating-point
division support, the exact coordinate-space finite-Loewner event, and the
budget inequality that absorbs the rounded objective perturbations. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hε : ε < 1)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j)
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hE, hbudget⟩
    have hpres :
        PreservesLSObjective A b (SA ω) (Sb ω) ε :=
      preservesLSObjective_of_coordinate_finiteLoewner_error
        A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
        (hsketch ω)
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Finite-Loewner exact sketch preservation plus explicit rounded-objective
    budgets and a solver objective gap gives a high-probability approximate
    rounded-solver objective bound.

This is the solver-facing version of
`eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event`. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt solverGap : Ω → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hε : ε < 1)
    (hhat : ∀ ω,
      IsLeastSquaresApproxMinimizer (SAr ω) (Sbr ω) (xHat ω)
        (solverGap ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j)
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hE, hbudget⟩
    have hpres :
        PreservesLSObjective A b (SA ω) (Sb ω) ε :=
      preservesLSObjective_of_coordinate_finiteLoewner_error
        A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
        (hsketch ω)
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- A coordinate-space operator-event probability implies the randomized
    least-squares objective guarantee for the sketched minimizer. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hprob : α ≤ P.eventProb {ω | opNorm2Le (E ω) ε})
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hpresProb :
      α ≤ P.eventProb
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} :=
    eventProb_preservesLSObjective_of_coordinate_quadratic_error
      P A b SA Sb coord E hε_nonneg hprob horig hsketch
  exact
    eventProb_lsObjective_le_one_add_eta_of_preserves
      P A b SA Sb xHat xOpt hε hfactor hpresProb hhat

/-- A two-sided finite-Loewner coordinate-space event implies the randomized
    least-squares objective guarantee for the sketched minimizer. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)})
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hpresProb :
      α ≤ P.eventProb
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} :=
    eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error
      P A b SA Sb coord E hprob horig hsketch
  exact
    eventProb_lsObjective_le_one_add_eta_of_preserves
      P A b SA Sb xHat xOpt hε hfactor hpresProb hhat

/-- Leverage-score row sampling supplies the coordinate-space operator event
    needed by the least-squares bridge, provided the original and sketched
    objectives have the stated coordinate representation. -/
theorem leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j *
            matMulVec d
              (fun j k => rowSampleGram s U samples j k - idMatrix d j k)
              (coord x) j) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let P := leverageTraceProbability (steps := s) U hU hd
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  have hprob :
      1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
        P.eventProb {samples | opNorm2Le (E samples) ε} := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon
        U hU hd hs hε_pos
  exact
    eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      P A b SA Sb coord E xHat xOpt (le_of_lt hε_pos) hprob hε hfactor
      hhat horig hsketch

/-- Exact leverage-score row-sampled least-squares objective guarantee with the
    concrete Algorithm 2 sampled rows of `A` and `b`.

The only remaining representation hypothesis is the mathematical statement
that each original residual has coordinates in the rows of the leverage basis
`U`.  The sampled/sketched objective representation itself is proved locally by
`rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error`. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples)
          (xHat samples))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      A b U hU hd hs
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      coord xHat xOpt hε_pos hε hfactor hhat horig
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples coord hres x)

/-- Exact leverage-score row-sampled least-squares objective guarantee using
    canonical residual coordinates.

This removes the arbitrary coordinate map from
`leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates`.
The remaining mathematical condition is that every residual `A x - b` lies in
the column span of the orthonormal-column matrix `U`.  Constructing such a `U`
from an augmented residual space is the separate QR/SVD/rank foundation. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples)
          (xHat samples))
    (hcol : ResidualsInColumnSpace A b U) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates
      A b U hU hd hs (residualCoordinates A b U) xHat xOpt hε_pos hε
      hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U hU hcol x)
      (fun x i => hcol x i)

/-- Exact leverage-score row-sampled least-squares objective guarantee using
    the orthonormal basis of the augmented data span `span{columns(A), b}`.

This closes the low-dimensional basis-construction dependency for equation
(8): the leverage dimension is now the explicit finite dimension of the
augmented data span.  The hypothesis `hd` rules out the degenerate zero-span
case, where the equation (6) leverage denominator would be zero. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 0 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s
            (augmentedSpanBasisMatrix A b) A samples)
          (rowSampleLSVectorWithBasisScale s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - 1 / ((s : ℝ) *
        (ε / (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
      A b (augmentedSpanBasisMatrix A b)
      (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd hs
      xHat xOpt hε_pos hε hfactor hhat
      (residualsInColumnSpace_augmentedSpanBasisMatrix A b)

/-- Source-aligned Bennett sample-budget version of the augmented-span
    row-sampled least-squares objective theorem.

This composes the sharper finite-Loewner equation (7) theorem with the
least-squares objective bridge.  The dimension in the Bennett budget is the
finite rank of `span{columns(A), b}`. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s
            (augmentedSpanBasisMatrix A b) A samples)
          (rowSampleLSVectorWithBasisScale s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hprob :
      1 - δ ≤ P.eventProb
        {samples |
          finiteLoewnerLe (E samples)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E samples j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)} := by
    simpa [P, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
      P A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      hprob hε hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
  simpa [P, U, d] using hmain

/-- Concrete identity-basis specialization of the exact leverage-score
    row-sampled least-squares objective guarantee.

With \(U=I_m\), equation (6) gives uniform row probabilities and every residual
is automatically in the span of `U`.  This closes a fully concrete finite-row
instance of the least-squares bridge.  It is intentionally weaker than the
survey's low-dimensional augmented-basis theorem, where \(d\) should be the
rank of the residual subspace rather than \(m\). -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_idBasis
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s (idMatrix m) A samples)
          (rowSampleLSVectorWithBasisScale s (idMatrix m) b samples)
          (xHat samples)) :
    1 - 1 / ((s : ℝ) * (ε / (m : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) (idMatrix m)
          (hasOrthonormalColumns_idMatrix m) hm).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
      A b (idMatrix m) (hasOrthonormalColumns_idMatrix m) hm hs
      xHat xOpt hε_pos hε hfactor hhat
      (residualsInColumnSpace_idMatrix A b)

/-- Fully floating-point leverage-score row sampling supplies the
    coordinate-space operator event needed by the least-squares bridge, with
    the row-scaling and dot-product perturbation budget included in the
    preservation radius. -/
theorem leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
    (fp : FPModel) {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε)
    (hradius :
      ε + rowSampleGramFullFpPerturbBudget fp s U < 1)
    (hfactor :
      (1 + (ε + rowSampleGramFullFpPerturbBudget fp s U)) /
          (1 - (ε + rowSampleGramFullFpPerturbBudget fp s U)) ≤
        1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j *
            matMulVec d
              (fun j k =>
                fl_rowSampleGramDot fp s U samples j k - idMatrix d j k)
              (coord x) j) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let P := leverageTraceProbability (steps := s) U hU hd
  let radius : ℝ := ε + rowSampleGramFullFpPerturbBudget fp s U
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k =>
      fl_rowSampleGramDot fp s U samples j k - idMatrix d j k
  have hprob :
      1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
        P.eventProb {samples | opNorm2Le (E samples) radius} := by
    simpa [P, E, radius] using
      leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget
        fp U hU hd hs hγ hε_pos
  have hradius_nonneg : 0 ≤ radius := by
    dsimp [radius]
    exact add_nonneg (le_of_lt hε_pos)
      (rowSampleGramFullFpPerturbBudget_nonneg fp s U)
  exact
    eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      P A b SA Sb coord E xHat xOpt hradius_nonneg hprob hradius
      (by simpa [radius] using hfactor) hhat horig hsketch

/-- Fully floating-point least-squares objective transfer using the
    augmented-span basis.

This specializes
`leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`
to the orthonormal basis of `span{columns(A), b}`.  It discharges the
coordinate/original-objective side of the FP transfer locally.  The theorem is
still an objective-level transfer: the supplied sketched objective must have
the stated rounded-Gram quadratic representation. -/
theorem leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 0 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε)
    (hradius :
      ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b) < 1)
    (hfactor :
      (1 + (ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b))) /
          (1 - (ε + rowSampleGramFullFpPerturbBudget fp s
            (augmentedSpanBasisMatrix A b))) ≤
        1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq
          (residualCoordinates A b (augmentedSpanBasisMatrix A b) x) +
          ∑ j : Fin (Module.finrank ℝ (augmentedDataSpan A b)),
            residualCoordinates A b (augmentedSpanBasisMatrix A b) x j *
              matMulVec (Module.finrank ℝ (augmentedDataSpan A b))
                (fun j k =>
                  fl_rowSampleGramDot fp s
                    (augmentedSpanBasisMatrix A b) samples j k -
                    idMatrix (Module.finrank ℝ (augmentedDataSpan A b)) j k)
                (residualCoordinates A b
                  (augmentedSpanBasisMatrix A b) x) j) :
    1 - 1 / ((s : ℝ) *
        (ε / (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      fp A b (augmentedSpanBasisMatrix A b)
      (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd hs hγ
      SA Sb (residualCoordinates A b (augmentedSpanBasisMatrix A b))
      xHat xOpt hε_pos hradius hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      hsketch

/-- Source-aligned Bennett sample-budget version of the floating-point
    augmented-span least-squares objective theorem.

The exact sampling event is the sharper finite-Loewner equation (7) theorem;
the floating-point event adds the rounded row-scaling/dot-product Gram budget
to the preservation radius before applying the least-squares bridge. -/
theorem leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hradius :
      ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b) < 1)
    (hfactor :
      (1 + (ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b))) /
          (1 - (ε + rowSampleGramFullFpPerturbBudget fp s
            (augmentedSpanBasisMatrix A b))) ≤
        1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq
          (residualCoordinates A b (augmentedSpanBasisMatrix A b) x) +
          ∑ j : Fin (Module.finrank ℝ (augmentedDataSpan A b)),
            residualCoordinates A b (augmentedSpanBasisMatrix A b) x j *
              matMulVec (Module.finrank ℝ (augmentedDataSpan A b))
                (fun j k =>
                  fl_rowSampleGramDot fp s
                    (augmentedSpanBasisMatrix A b) samples j k -
                    idMatrix (Module.finrank ℝ (augmentedDataSpan A b)) j k)
                (residualCoordinates A b
                  (augmentedSpanBasisMatrix A b) x) j) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let radius : ℝ := ε + rowSampleGramFullFpPerturbBudget fp s U
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k =>
      fl_rowSampleGramDot fp s U samples j k - idMatrix d j k
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hprob :
      1 - δ ≤ P.eventProb
        {samples |
          finiteLoewnerLe (E samples)
            (fun j k : Fin d => radius * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E samples j k)
            (fun j k : Fin d => radius * finiteIdMatrix j k)} := by
    simpa [P, E, U, d, radius, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        fp (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hγ hε_pos hδ
        hbudgetUpper hbudgetLower
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
      P A b SA Sb (residualCoordinates A b U) E xHat xOpt
      hprob (by simpa [radius, U] using hradius)
      (by simpa [radius, U] using hfactor) hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (by simpa [E, U, d] using hsketch)
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for the literal rounded
    sampled/scaled least-squares construction.

This is the high-probability composition for the concrete rounded `A,b` sketch.
It reuses the exact finite-Loewner equation (7) concentration theorem and the
literal rounded objective perturbation theorem.  The remaining floating-point
size requirement is exposed as `hobjectiveBudget`: the sum of the explicit
rounded-objective budgets at the rounded minimizer and at `xOpt` must fit in
the slack between the exact sketch factor and the requested `1 + η` factor. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  let Exact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe (E samples)
        (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe (fun j k : Fin d => -E samples j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k)}
  let Target : Set (RowTrace m s) :=
    {samples |
      samples ∈ Good ∧
      (finiteLoewnerLe (E samples)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E samples j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
      rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples) +
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt}
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hExact :
      1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd)
    simpa [P, Good, leverageTraceProbability, U] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGoodLower : 1 - (0 : ℝ) ≤ P.eventProb Good := by
    linarith
  have hinter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P Exact Good δ 0 hExact hGoodLower
  have hTargetProb : 1 - δ ≤ P.eventProb Target := by
    have hsubset : Exact ∩ Good ⊆ Target := by
      intro samples hsamples
      rcases hsamples with ⟨hexact, hgood⟩
      have hgood' : rowTracePositiveProb U samples := by
        simpa [Good] using hgood
      exact ⟨hgood, hexact, by
        simpa [Target, U] using hobjectiveBudget samples hgood'⟩
    have hmono := FiniteProbability.eventProb_mono P hsubset
    have hδsum : δ + 0 = δ := by ring
    nlinarith
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event
      P Good A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (fun samples => fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples))
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt)
      (ε := ε) (η := η) (α := 1 - δ)
      (by simpa [Target] using hTargetProb)
      hε hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples (xHat samples) hs
          (by simpa [Good] using hgood))
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples xOpt hs
          (by simpa [Good] using hgood))
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for the literal rounded
    sampled/scaled least-squares construction with an explicit solver gap.

This is the solver-facing bridge for equation (8).  The vector `xHat samples`
need only be an additive-gap approximate minimizer of the literal rounded
sampled problem.  The theorem keeps that solver gap explicit: it must fit,
together with the two rounded-objective perturbation budgets, inside the same
objective slack.  It does not prove a concrete QR/preconditioner gap bound. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (solverGap : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            solverGap samples ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hhat :
      ∀ samples,
        IsLeastSquaresApproxMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples) (solverGap samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  let Exact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe (E samples)
        (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe (fun j k : Fin d => -E samples j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k)}
  let Target : Set (RowTrace m s) :=
    {samples |
      samples ∈ Good ∧
      (finiteLoewnerLe (E samples)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E samples j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
      rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples) +
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt +
        solverGap samples ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt}
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hExact :
      1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd)
    simpa [P, Good, leverageTraceProbability, U] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGoodLower : 1 - (0 : ℝ) ≤ P.eventProb Good := by
    linarith
  have hinter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P Exact Good δ 0 hExact hGoodLower
  have hTargetProb : 1 - δ ≤ P.eventProb Target := by
    have hsubset : Exact ∩ Good ⊆ Target := by
      intro samples hsamples
      rcases hsamples with ⟨hexact, hgood⟩
      have hgood' : rowTracePositiveProb U samples := by
        simpa [Good] using hgood
      exact ⟨hgood, hexact, by
        simpa [Target, U] using hobjectiveBudget samples hgood'⟩
    have hmono := FiniteProbability.eventProb_mono P hsubset
    have hδsum : δ + 0 = δ := by ring
    nlinarith
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event
      P Good A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (fun samples => fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples))
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt)
      solverGap
      (ε := ε) (η := η) (α := 1 - δ)
      (by simpa [Target] using hTargetProb)
      hε hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples (xHat samples) hs
          (by simpa [Good] using hgood))
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples xOpt hs
          (by simpa [Good] using hgood))
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares with a componentwise solver forward-error
    certificate.

This specializes the solver-gap theorem to the common situation where a solver
returns `xHat samples` together with a componentwise distance certificate
`solverDx samples` from an exact minimizer `xStar samples` of the rounded
sampled problem.  The induced objective gap is explicit and follows from the
local residual/objective perturbation algebra above. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (solverDx : RowTrace m s → Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples) (solverDx samples) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hdx : ∀ samples j, 0 ≤ solverDx samples j)
    (hclose : ∀ samples j,
      |xHat samples j - xStar samples j| ≤ solverDx samples j) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap
      fp A b hd hs xHat xOpt
      (fun samples =>
        lsSolutionForwardObjectiveGap
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples) (solverDx samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget ?_
  intro samples
  exact
    isLeastSquaresApproxMinimizer_of_solution_abs_le
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (xHat samples) (xStar samples) (solverDx samples)
      (hstar samples) (hdx samples) (hclose samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is certified by a
    perturbed normal-equation system.

The theorem reuses the local Gram-system forward-error theorem to construct
the componentwise `solverDx` certificate consumed by
`..._and_forward_error`.  It still keeps the perturbed-system certificate
explicit; deriving that certificate from a concrete QR factorization,
preconditioner, or iterative solver is a separate downstream theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (ΔG : RowTrace m s → Fin n → Fin n → ℝ)
    (Δg : RowTrace m s → Fin n → ℝ)
    (εG εg : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (gramForwardSolverDx (ATA_inv samples) (εG samples)
                (εg samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hPerturbed : ∀ samples i,
      matMulVec n
        (fun j k =>
          lsNormalMatrix
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples) j k +
            ΔG samples j k)
        (xHat samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i +
          Δg samples i)
    (hΔG_bound : ∀ samples i j, |ΔG samples i j| ≤ εG samples)
    (hΔg_bound : ∀ samples i, |Δg samples i| ≤ εg samples)
    (hεG : ∀ samples, 0 ≤ εG samples)
    (hεg : ∀ samples, 0 ≤ εg samples) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs xHat xStar xOpt
      (fun samples =>
        gramForwardSolverDx (ATA_inv samples) (εG samples)
          (εg samples) (xHat samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    exact
      gramForwardSolverDx_nonneg
        (ATA_inv samples) (εG samples) (εg samples) (xHat samples)
        (hεG samples) (hεg samples) j
  · intro samples j
    exact
      gram_forward_error_certificate_of_perturbed_gram_system
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (xHat samples)
        (hExact samples) (ΔG samples) (Δg samples)
        (hPerturbed samples) (εG samples) (εg samples)
        (hΔG_bound samples) (hΔg_bound samples)
        (hεG samples) (hεg samples) j

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is represented by
    the local `LSQRSolveBackwardError` specification.

This closes the small adapter from the repository's least-squares QR
backward-error vocabulary to the RandNLA objective transfer.  It still does
not prove the QR/preconditioner implementation theorem that would construct
the `LSQRSolveBackwardError` structure for a concrete solver. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hBack : ∀ samples,
      LSQRSolveBackwardError n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xHat samples) (c_G samples) (c_g samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs xHat xStar xOpt
      (fun samples =>
        lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
          (c_g samples) (xHat samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    have hBackSamples := hBack samples
    rcases hBackSamples.result with ⟨ΔG, _Δg, _hPerturbed, hΔG_frob, _hΔg_bound⟩
    have hcG : 0 ≤ c_G samples := le_trans (frobNorm_nonneg ΔG) hΔG_frob
    exact
      lsQRSolveBackwardSolverDx_nonneg
        (ATA_inv samples) (c_G samples) (c_g samples) (xHat samples)
        hcG j
  · intro samples j
    exact
      gram_forward_error_certificate_of_ls_qr_solve_backward_error
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (xHat samples) (hExact samples)
        (c_G samples) (c_g samples) (hBack samples) j

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is a stored
    Householder QR handoff satisfying the packaged off-diagonal-control
    invariant.

The theorem composes the repository's concrete stored-QR
`LSQRSolveBackwardError` theorem with the RandNLA objective transfer.  The
remaining QR/preconditioner obligation is intentionally visible as the single
route-1 invariant `StoredQROffDiagonalControlInvariant`: a concrete QR route
must prove it from source-specific pivoting, ordering, or off-diagonal-growth
assumptions before this becomes a fully implementation-backed theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff : ∀ samples,
      StoredQROffDiagonalControlInvariant hmn fp
        (A_hat samples) (b_hat samples) (alpha samples))
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hoff samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with the packaged invariant built from
    local diagonal dominance and the canonical finite-max product-smallness
    inequality.

This is the direct equation (8) wrapper for the two visible route-1 fields.  It
does not prove local diagonal dominance or scalar finite-max smallness from the
stored recurrence; it only prevents the packaged invariant from becoming an
extra hidden hypothesis once those two source/domain facts are supplied
samplewise. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
      (fun k hk => hDD samples k hk) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with the packaged invariant built from the
    canonical finite-max rational-gamma source-denominator cap route.

This is the probability-level sibling of the solver theorem
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`.
It keeps the remaining QR arithmetic obligations samplewise and explicit:
local diagonal dominance, source-shaped Householder denominator nonbreakdown,
the unit-roundoff cap, the rational-cap validity condition, and the canonical
scalar finite-max smallness inequality. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) Ucap hm
      (fun k hk => hDD samples k hk)
      hUcap_nonneg (hden samples) hu huCap (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with source denominator nonbreakdown derived
    from signed-alpha/trailing-norm data.

    This is the probability-level source-nonbreakdown reduction of
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
    The raw `v^T v != 0` field is replaced by samplewise positive active
    trailing norms; the existing signed-alpha definition supplies the square
    equation and sign condition used by the local Householder nonbreakdown
    theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (htrailingPos : ∀ samples k (hk : k < n),
      0 < householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0 := by
    intro samples k hk
    have halpha :
        alpha samples k * alpha samples k =
          householderTrailingNorm2Sq s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) := by
      rw [hAlphaDef samples k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
          s ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩)
    have hsign :
        alpha samples k *
            A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
      rw [hAlphaDef samples k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
          s ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩)
    exact
      householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
        s ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)
        halpha (htrailingPos samples k hk) hsign
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hden hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with source denominator nonbreakdown derived
    from leading-block determinant data.

    This is the probability-level determinant/rank specialization of
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
    The samplewise previous/current leading determinant facts and lower-zero
    shape imply positive active trailing norms, which feed the existing
    signed-alpha source-nonbreakdown route. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ samples k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat samples k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have htrailingPos : ∀ samples k (hk : k < n),
      0 < householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples k hk
    exact
      householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
        (A_hat samples k) (lt_of_lt_of_le hk hmn) hk
        (hdetPrev samples k hk) (hdetLead samples k hk)
        (hlowerPrev samples k hk)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg htrailingPos hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with current leading-block nonsingularity
    derived from local diagonal dominance.

    Compared with
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`,
    this wrapper removes the samplewise current leading-block determinant
    field.  The previous transposed leading-block determinant remains visible,
    while the current one follows from `IsDiagDominantUpper`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ samples k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat samples k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hdetPrev
      (fun samples k hk =>
        det_ne_zero_of_diagDominantUpper (k + 1)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (hDD samples k hk))
      hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with both previous and current local determinant
    fields derived from local diagonal dominance.

Compared with
`..._stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`,
this wrapper also removes the samplewise previous transposed leading-block
determinant field.  The previous determinant is obtained from the same
samplewise `IsDiagDominantUpper` leading-block hypothesis via the local
top-left-block determinant adapter; the previous lower-zero field remains
visible because it is still needed by the trailing-norm bridge. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg
      (fun samples k hk =>
        qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
          (A_hat samples k) (le_of_lt (lt_of_lt_of_le hk hmn))
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
          (hDD samples k hk))
      hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma diagonal-dominant QR route, with the previous-column
    lower-zero shape derived from the stored panel recurrence.

This removes the explicit samplewise `hlowerPrev` field from
`..._stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
The only lower-zero information used is the repository theorem that the stored
Householder panel loop preserves completed columns and writes exact zeros below
each pivot. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0 := by
    intro samples
    exact
      storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
        fp hmn (A_hat samples) (alpha samples) (hStepA samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    with `0 ≤ Ucap` derived from the unit-roundoff cap.

This removes one proof-artifact hypothesis from the high-probability Algorithm 2
least-squares objective theorem: the FP model gives `0 ≤ fp.u`, so `fp.u ≤ Ucap`
already implies `0 ≤ Ucap`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hUcap_nonneg : 0 ≤ Ucap := le_trans fp.u_nonneg hu
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hu huCap hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    with all gamma-validity guards derived from the displayed unit-roundoff cap.

The assumptions `fp.u ≤ Ucap` and `(s : ℝ) * Ucap < 1` imply
`gammaValid fp s`; since the sampled problem has `n ≤ s`, they also imply
`gammaValid fp n`. This removes the remaining redundant floating-point
validity hypotheses from the cap-based high-probability Algorithm 2 surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s Ucap hu huCap
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD hu huCap
      hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    specialized to the actual unit roundoff of the FP model.

This removes the displayed-cap field `fp.u ≤ Ucap` from the high-probability
Algorithm 2 surface by choosing `Ucap = fp.u`.  The sampled-dimension validity
guard `gammaValid fp s` and the actual-unit scalar smallness condition remain
visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have huCap : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      fp.u hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hInitA hInitb hStepA hStepb hAlphaDef hDD
      (le_rfl : fp.u ≤ fp.u) huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the stored-lower canonical
    rational-gamma QR route, specialized to the actual unit roundoff and with the
    operation-validity guard displayed as `(s : ℝ) * fp.u < 1`.

This keeps the real numerical smallness hypothesis visible and removes the
abstract `gammaValid fp s` assumption from the probability-level statement.  The
canonical scalar smallness inequality remains an explicit QR-domain hypothesis. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      fp.u hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hInitA hInitb hStepA hStepb hAlphaDef hDD
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with compact-product smallness supplied by
    the canonical finite maximum of the explicit compact Householder norm
    coefficient.

This is the coefficient-max sibling of
`..._offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`.  It still
does not prove local diagonal dominance or scalar coefficient-max smallness from
the stored recurrence; it only threads the already formalized coefficient-max
product theorem into the probability-level equation (8) surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (((n : ℝ) *
                ((n : ℝ) *
                  storedQRCompactStepNormBudgetCoeffBudget hmn fp
                    (A_hat samples) (alpha samples) +
                  storedQRCompactStepNormBudgetCoeffBudget hmn fp
                    (A_hat samples) (alpha samples))) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
      (fun k hk => hDD samples k hk) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is a stored
    Householder QR handoff satisfying the source-shaped off-diagonal-control
    certificate.

The theorem composes the repository's concrete stored-QR
`LSQRSolveBackwardError` theorem with the RandNLA objective transfer.  The
remaining QR/preconditioner obligations are intentionally visible: the stored
loop must supply signed-alpha steps, source off-diagonal control, and the
budget equations identifying the reported solution and radii with the final
back-substitution handoff. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff : ∀ samples,
      StoredQRSourceOffDiagonalControl hmn fp
        (A_hat samples) (b_hat samples) (alpha samples))
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl
          hmn fp (A_hat samples) (b_hat samples) (alpha samples)
          (hoff samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the primitive
    off-diagonal-control route.

This is the probability-level companion to
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`.
The stored recurrence supplies triangular shape, while the caller supplies the
genuine route-1 fields: leading-block nonsingularity, norm-square
nonbreakdown, row-wise off-diagonal domination, and per-pivot compact-product
smallness.  Thus the theorem closes the objective-transfer assembly edge
without hiding the remaining computed-loop invariant obligations. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiag : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product
          hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
          (hStepA samples) (hAlphaDef samples) (hbudgetNormSq samples)
          (hdetLead samples) (hoffdiag samples) (hproduct samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver uses
    the packaged displayed row-budget control certificate.

This is the equation (8) probability-level companion to
`StoredQRDisplayedRowBudgetControl`.  It keeps the Cox--Higham row-growth and
diagonal lower-bound/nonbreakdown fields visible as a single samplewise domain
certificate, then reuses the source-shaped stored-QR objective theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product
          hmn fp (A_hat samples) (b_hat samples) (alpha samples)
          (rowBudget samples) hm (hStepA samples) (hAlphaDef samples)
          (hbudgetNormSq samples) (hdetLead samples) (hrowControl samples)
          (hproduct samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose displayed row-budget
    stored-QR solver certificate derives norm-square nonbreakdown from local
    `κ∞`/dual compact-budget data.

This is the row-budget-control companion to
`..._stored_qr_rowBudgetControl_solver`.  It removes the raw samplewise
norm-square nonbreakdown hypothesis by reusing the local leading-block inverse
budget route, while keeping the displayed row-budget control, determinant, and
compact-product hypotheses explicit. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
      fp A b hd hs hmn A_hat b_hat alpha rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hrowControl hproduct
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose displayed row-budget
    stored-QR solver certificate uses the finite global compact-product budget.

This is the finite-budget version of
`..._rowBudgetControl_kappaInf_dualBudget_solver`: the scalar condition
`storedQRCompactSequenceProductBudget < 1` is converted locally into the
per-pivot compact-product inequalities consumed by the row-budget-control
handoff.  The theorem still keeps the displayed row-budget certificate and the
local `κ∞`/dual compact-budget data visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1 := by
    intro samples k hk
    let kk : Fin n := ⟨k, hk⟩
    have hle :
        storedQRCompactSequenceProductExpr hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) kk ≤
          storedQRCompactSequenceProductBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) :=
      storedQRCompactSequenceProductExpr_le_budget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) kk
    exact lt_of_le_of_lt (by
      simpa [storedQRCompactSequenceProductExpr, kk] using hle)
      (hglobalProduct samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hrowControl
      hproduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the scalar row-max defect
    QR route.

This is the probability-level companion to
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`.
It keeps the scalar samplewise condition
`storedQRRowMaxDiagDefectBudget <= 0` visible and converts it to the packaged
displayed row-budget certificate locally.  The theorem also keeps the
norm-square nonbreakdown, determinant, and finite global compact-product
conditions explicit. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hdefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let rowBudget :
      RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ :=
    fun samples k hk i =>
      qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i
  have hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples)
        (rowBudget samples) := by
    intro samples
    exact
      StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos
        hmn (A_hat samples) (hdefect samples)
  have hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1 := by
    intro samples k hk
    let kk : Fin n := ⟨k, hk⟩
    have hle :
        storedQRCompactSequenceProductExpr hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) kk ≤
          storedQRCompactSequenceProductBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) :=
      storedQRCompactSequenceProductExpr_le_budget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) kk
    exact lt_of_le_of_lt (by
      simpa [storedQRCompactSequenceProductExpr, kk] using hle)
      (hglobalProduct samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
      fp A b hd hs hmn A_hat b_hat alpha rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hrowControl hproduct
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the scalar row-max defect
    QR route with gamma-validity derived from actual unit roundoff.

This is the actual-unit-roundoff sibling of
`..._rowMaxDiagDefect_globalProduct_solver`: the sampled-dimension scalar guard
`(s : ℝ) * fp.u < 1` supplies both `gammaValid fp s` and, since `n ≤ s`,
`gammaValid fp n`.  The scalar row-defect, determinant, norm-square
nonbreakdown, and global compact-product hypotheses remain visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hdefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hbudgetNormSq
      hdetLead hdefect hglobalProduct hxHat hcG hcg

/-- Active-max-pivot global compact-step version of the row-budget-control
    equation (8) theorem.

This theorem connects the active-max-pivot packaged row-budget constructor to
the RandNLA probability layer.  It derives the samplewise
`StoredQRDisplayedRowBudgetControl` certificate from the finite active
max-pivot policy, local `κ∞`/dual compact-budget data, and the global
compact-step recurrence, then applies the finite global-product row-budget
objective theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ :=
    fun samples k _hk _i => stageBudget samples k
  have hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples)
        (rowBudget samples) := by
    intro samples
    exact
      StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
        (hdetLead samples) (hK samples) (hκ samples) (hκbudget samples)
        (hbudgetDual samples) (hinitBlock samples) (hglobalBudget samples)
        (hBudget_nonneg samples) (hBudget_mono samples) (hBudget_diag samples)
        (hpivotChoice samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hrowControl
      hglobalProduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate is discharged by the active/prefix global compact-step route.

This is the equation (8) assembly theorem for the current Cox--Higham
active/prefix branch: it combines the RandNLA objective transfer with the
stored QR solver certificate that derives completed-column preservation and
per-pivot compact-product conditions internally.  The genuinely source-specific
QR fields remain visible samplewise assumptions: norm-square nonbreakdown,
local leading-block nonsingularity, diagonal lower bounds, pivot maximality,
the global compact-step recurrence, and the global product-smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hbudgetNormSq samples) (hdetLead samples) (hinit samples)
      (hinitBlock samples) (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hBudget_diag samples) (hpivotMax samples)
      (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem for the active/prefix global
    compact-step route without a separate global stage-budget monotonicity
    hypothesis.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_solver`, but the samplewise
monotonicity field is replaced by the horizon-clamped QR budget wrapper from
the stored-QR source-control library. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hbudgetNormSq samples) (hdetLead samples) (hinit samples)
      (hinitBlock samples) (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_diag samples) (hpivotMax samples) (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem whose active/prefix stored-QR
    solver certificate derives norm-square nonbreakdown from local `κ∞`/dual
    compact-budget data.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_solver`, but it replaces the raw
samplewise `hbudgetNormSq` assumption by the structured leading-block
inverse-budget route already proved in the QR/least-squares library. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped sibling of the `κ∞`/dual-budget active/prefix global-product
    equation (8) theorem.

This removes the samplewise global stage-budget monotonicity field while still
deriving norm-square nonbreakdown from the local leading-block
`κ∞`/self-norm and dual compact-budget route. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot version of the source-aligned Bennett sample-budget theorem
    for the active/prefix global compact-step route.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver`, but it
replaces the raw samplewise pivot-maximality hypothesis by the algorithmic
policy that the displayed pivot column is `householderActiveMaxPivotColumn` for
the current active block. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) l ≤
        householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) ⟨t, ht⟩ := by
    intro samples t ht l hl
    have hmax :=
      householderActiveMaxPivotColumn_pivot_max
        ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t) l hl
    have hnormEq :
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t)
            (householderActiveMaxPivotColumn
              ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t)) =
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩ := by
      rw [← hpivotChoice samples t ht]
    exact hmax.trans_eq hnormEq
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped active-max-pivot version of the source-aligned Bennett
    sample-budget theorem for the active/prefix global compact-step route.

This is the same equation (8) assembly as
`..._activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`, but
the samplewise global stage-budget monotonicity field is derived internally
from the finite compact-step recurrence through the horizon-clamped
`κ∞`/dual-budget wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) l ≤
        householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) ⟨t, ht⟩ := by
    intro samples t ht l hl
    have hmax :=
      householderActiveMaxPivotColumn_pivot_max
        ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t) l hl
    have hnormEq :
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t)
            (householderActiveMaxPivotColumn
              ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t)) =
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩ := by
      rw [← hpivotChoice samples t ht]
    exact hmax.trans_eq hnormEq
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot equation (8) wrapper with visible row-max assumptions.

This is the same high-probability active/prefix QR assembly as
`..._activeMaxPivot_kappaInf_dualBudget_solver`, but it exposes the two
row-max fields needed by the scalar stage-diagonal route:
`storedQRRowMaxDiagDefectBudget <= 0` and the displayed comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget`.  The diagonal lower-bound
family is derived internally by the row-max bridge before applying the existing
active-max-pivot probability theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i| := by
    intro samples
    exact
      storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos
        hmn (A_hat samples) (stageBudget samples)
        (storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax
          hmn (A_hat samples) (stageBudget samples) (hrowDefect samples)
          (hstage_le_rowMax samples))
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped visible row-max active-max-pivot equation (8) wrapper.

This is the same theorem surface as
`..._activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`,
but it removes the samplewise global stage-budget monotonicity field by deriving
the diagonal lower-bound family from the row-max assumptions and then applying
the horizon-clamped active-pivot `κ∞`/dual-budget wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i| := by
    intro samples
    exact
      storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos
        hmn (A_hat samples) (stageBudget samples)
        (storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax
          hmn (A_hat samples) (stageBudget samples) (hrowDefect samples)
          (hstage_le_rowMax samples))
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Actual-unit-roundoff sibling of the probability-level visible row-max
    active-pivot equation (8) theorem.

The scalar sampled-dimension guard `(s : ℝ) * fp.u < 1` supplies both
`gammaValid fp s` and, because `n ≤ s`, `gammaValid fp n`.  The row-max
defect, stage-budget/row-max comparison, determinant/conditioning,
dual compact-budget, active-pivot policy, and global compact-product
assumptions remain visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect hstage_le_rowMax
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped actual-unit-roundoff version of the visible row-max
    active-max-pivot equation (8) wrapper.

This composes the actual-unit-roundoff validity reduction with the
horizon-clamped row-max theorem, so the sampled theorem surface exposes
`(s : ℝ) * fp.u < 1` instead of sampled `gammaValid` fields and does not expose
the samplewise global stage-budget monotonicity hypothesis. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect hstage_le_rowMax hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot equation (8) wrapper with finite row-max scalar defects.

This sampled theorem replaces the displayed samplewise comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget` by the scalar finite maximum
condition `storedQRStageRowMaxComparisonDefectBudget <= 0`, then applies the
existing visible row-max probability theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped scalar-comparison active-pivot equation (8) wrapper.

This is the explicit-`gammaValid` sibling of the scalar finite comparison
probability theorem.  It extracts the displayed comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget` from the scalar comparison
defect and then calls the horizon-clamped visible row-max wrapper, so the
samplewise global stage-budget monotonicity field is not part of this theorem
surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper.

This is the probability-level sibling of the local diagonal-dominant
active-pivot scalar-comparison route: samplewise diagonal dominance supplies the
local determinant and row-max scalar-defect fields, while the scalar comparison
defect supplies the remaining stage-budget/row-max comparison through the
already-formalized finite package. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro samples k hk
    exact
      det_ne_zero_of_diagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hDD samples k hk)
  have hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0 := by
    intro samples
    exact
      storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant
        hmn (A_hat samples) (hDD samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect hcomparison
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper with
    compact-product smallness supplied by the canonical finite-max scalar.

This is the probability-level finite-max sibling of
`..._activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_...`:
for each sampled stored-QR trace, local diagonal dominance and the finite-max
smallness inequality derive the raw global product field before the existing
active-pivot scalar-comparison theorem is applied. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1 := by
    intro samples
    exact
      storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness
        hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
        (fun k => hDD samples k.val k.isLt) (hsmall samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hDD hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hcomparison hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper using the
    concrete dual-budget route.

This is the probability-level active-pivot finite-max theorem after eliminating
the auxiliary `κ`/`K` and dual compact-budget package.  For each sampled stored
QR trace, the concrete-dual source-control theorem derives norm-square
nonbreakdown from local diagonal dominance and the canonical finite-max
smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hcomparison samples) (hpivotChoice samples)
      (hsmall samples)

/-- Actual-unit-roundoff sibling of the sampled active finite-max concrete-dual
    equation (8) theorem.

The sampled `gammaValid fp s` and triangular `gammaValid fp n` hypotheses are
derived from `(s : ℝ) * fp.u < 1`.  The genuinely open QR-domain fields remain
visible samplewise: local diagonal dominance, signed-stage recurrence budgets,
active-pivot choice, scalar comparison defect, and finite-max product
smallness. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice hsmall hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper using the
    canonical source-denominator/rational-gamma compact-product cap.

This is the probability-level sibling of the active local source-denominator
handoff: for each sampled stored QR trace, the source-control certificate
derives the raw compact-product field from source-denominator nonbreakdown,
the unit-roundoff cap, and the canonical rational-gamma cap-smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) Ucap hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hcomparison samples) (hpivotChoice samples)
      hUcap_nonneg (hden samples) hu huCap (hsmall samples)

/-- Horizon-clamped sampled equation (8) wrapper using the canonical
    source-denominator/rational-gamma compact-product cap.

For each sampled stored QR trace, the global compact-step recurrence supplies
monotonicity on the QR horizon.  The local source-control certificate clamps
the budget after that horizon internally, so this probability surface no longer
exposes a samplewise global monotonicity assumption. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) Ucap hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hcomparison samples) (hpivotChoice samples) hUcap_nonneg
      (hden samples) hu huCap (hsmall samples)

/-- Actual-unit-roundoff sibling of the probability-level active
    source-denominator/cap scalar-comparison theorem.

This specializes the cap to `Ucap = fp.u` and derives the sampled
`gammaValid fp s` and triangular `gammaValid fp n` guards internally from
`(s : ℝ) * fp.u < 1`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g fp.u hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Actual-unit horizon-clamped sibling of the probability-level active
    source-denominator/cap scalar-comparison theorem.

This combines the horizon-clamped source-denominator handoff with the
`Ucap = fp.u` specialization, deriving the sampled `gammaValid` guards from
`(s : ℝ) * fp.u < 1` while leaving global stage-budget monotonicity off the
surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g fp.u hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Sampled actual-unit active source-denominator theorem with denominator
    nonbreakdown derived from the stored QR trace.

This stored-lower sibling removes the samplewise raw source-denominator field
from the equation (8) probability surface.  For every sampled trace, denominator
nonbreakdown follows from the stored recurrence, signed-alpha definition, and
local diagonal dominance before the existing actual-unit theorem is applied. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice
      (fun samples =>
        storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
          fp hmn (A_hat samples) (alpha samples)
          (hStepA samples) (hAlphaDef samples) (hDD samples))
      hsmall hxHat hcG hcg

/-- Horizon-clamped sampled actual-unit active source-denominator theorem with
    denominator nonbreakdown derived from the stored QR trace.

This is the stored-lower sibling of the horizon-clamped source-denominator
probability theorem: the trace itself supplies denominator nonbreakdown, and
the compact-step recurrence supplies the only monotonicity needed on the QR
horizon. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hcomparison hpivotChoice
      (fun samples =>
        storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
          fp hmn (A_hat samples) (alpha samples)
          (hStepA samples) (hAlphaDef samples) (hDD samples))
      hsmall hxHat hcG hcg

/-- Actual-unit-roundoff sibling of the probability-level scalar-comparison
    active-pivot equation (8) theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped actual-unit-roundoff sibling of the probability-level
    scalar-comparison active-pivot equation (8) theorem.

This removes the samplewise global budget-monotonicity field from the
actual-unit scalar-comparison surface by extracting the displayed row-max
comparison from the scalar defect and calling the horizon row-max wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect hcomparison hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate uses diagonal-dominant local leading blocks.

This is an equation (8) assembly route for the case where the displayed local
leading blocks are already diagonally dominant.  The diagonal-dominance
hypothesis supplies the off-diagonal/diagonal-lower-bound field directly, while
the `κ∞`/dual-budget hypotheses supply the norm-square nonbreakdown margin and
the finite global compact-product scalar supplies product smallness. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (κ samples) (K samples) hm (hStepA samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hK samples) (hκ samples)
      (hκbudget samples) (hbudgetDual samples) (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate uses diagonal-dominant local leading blocks and the canonical
    finite-max product-smallness scalar condition.

This is the same equation (8) assembly as
`..._diagDominant_globalProduct_kappaInf_dualBudget_solver`, but the raw
global-product hypothesis is replaced by one scalar inequality involving the
canonical finite maxima of the local diagonal-dominant inverse factors and
pivot-column norms for each sampled QR trace. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (κ samples) (K samples) hm (hStepA samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hK samples) (hκ samples)
      (hκbudget samples) (hbudgetDual samples) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares whose stored-QR solver is discharged by the
    concrete diagonal-dominant finite-max route.

Compared with
`..._diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`, this theorem
does not expose auxiliary `κ`/`K` sequences or a separate dual compact-budget
hypothesis.  The local least-squares theorem reuses the repository's concrete
diagonal-dominant inverse-budget route and the canonical finite-max scalar
smallness inequality. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hsmall samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares whose stored-QR solver is discharged by the
    concrete diagonal-dominant finite-max route, with local determinant
    nonzeroness derived from `IsDiagDominantUpper`.

Compared with
`..._diagDominant_finiteMaxSmallness_concreteDual_solver`, this theorem does
not expose a separate samplewise `hdetLead` field: the repository
`IsDiagDominantUpper` predicate already includes upper-triangular shape and
nonzero diagonal entries, hence local nonsingularity. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hDD samples) (hsmall samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is the concrete
    normal-equations/Cholesky method formalized in
    `LSNormalEquations.lean`.

This closes an implementation-backed solver certificate route: the local
normal-equations backward-error theorem supplies explicit perturbation radii,
and the local forward-error theorem turns them into the componentwise
`solverDx` certificate consumed by the RandNLA objective transfer.  This is
not a QR/preconditioner theorem; it is a concrete normal-equations solver
variant with its conditioning consequences exposed in the certificate. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (absATA : RowTrace m s → Fin n → Fin n → ℝ)
    (absATb : RowTrace m s → Fin n → ℝ)
    (C_hat : RowTrace m s → Fin n → Fin n → ℝ)
    (c_hat : RowTrace m s → Fin n → ℝ)
    (R_hat : RowTrace m s → Fin n → Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples
              (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (normalEqCholeskySolverDx (m := s) fp (ATA_inv samples)
                (absATA samples) (absATb samples) (R_hat samples)
                (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (habsATA : ∀ samples i j, 0 ≤ absATA samples i j)
    (habsATb : ∀ samples i, 0 ≤ absATb samples i)
    (hGram : ∀ samples,
      GramProductError n (C_hat samples)
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (absATA samples) (gamma fp s))
    (hGramVec : ∀ samples,
      GramVecError n (c_hat samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (absATb samples) (gamma fp s))
    (hChol : ∀ samples,
      CholeskyBackwardError n (C_hat samples) (R_hat samples)
        (gamma fp (n + 1)))
    (hR_diag : ∀ samples i, R_hat samples i i ≠ 0)
    (hγs : gammaValid fp s) (hγn1 : gammaValid fp (n + 1)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b
              (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs
      (fun samples =>
        normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))
      xStar xOpt
      (fun samples =>
        normalEqCholeskySolverDx (m := s) fp (ATA_inv samples)
          (absATA samples) (absATb samples) (R_hat samples)
          (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    exact
      normalEqCholeskySolverDx_nonneg (m := s) fp (ATA_inv samples)
        (absATA samples) (absATb samples) (R_hat samples)
        (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))
        (habsATA samples) (habsATb samples) hγs hγn1 j
  · intro samples j
    exact
      normal_equations_cholesky_forward_error_certificate (m := s) fp
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (hExact samples)
        (absATA samples) (absATb samples)
        (C_hat samples) (c_hat samples) (R_hat samples)
        (hGram samples) (hGramVec samples) (hChol samples)
        (hR_diag samples) hγs hγn1 j

/-- Fully floating-point least-squares objective transfer for the identity
    basis fallback.

This is the full-row-space counterpart of
`leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan`.
It is concrete and assumption-light, but uses `d = m` and therefore is not the
sharp low-dimensional leverage-score theorem. -/
theorem leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_idBasis
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε)
    (hradius :
      ε + rowSampleGramFullFpPerturbBudget fp s (idMatrix m) < 1)
    (hfactor :
      (1 + (ε + rowSampleGramFullFpPerturbBudget fp s (idMatrix m))) /
          (1 - (ε + rowSampleGramFullFpPerturbBudget fp s (idMatrix m))) ≤
        1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq (residualCoordinates A b (idMatrix m) x) +
          ∑ j : Fin m,
            residualCoordinates A b (idMatrix m) x j *
              matMulVec m
                (fun j k =>
                  fl_rowSampleGramDot fp s (idMatrix m) samples j k -
                    idMatrix m j k)
                (residualCoordinates A b (idMatrix m) x) j) :
    1 - 1 / ((s : ℝ) * (ε / (m : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s)
          (idMatrix m) (hasOrthonormalColumns_idMatrix m) hm).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      fp A b (idMatrix m) (hasOrthonormalColumns_idMatrix m) hm hs hγ
      SA Sb (residualCoordinates A b (idMatrix m)) xHat xOpt
      hε_pos hradius hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b (idMatrix m) (hasOrthonormalColumns_idMatrix m)
          (residualsInColumnSpace_idMatrix A b) x)
      hsketch

end NumStability
