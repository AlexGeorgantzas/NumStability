import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Normwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Rowwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Foundations.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.RankStability.FullRowRank.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.TriangularSolves.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.UnderdeterminedSpec
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation01.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation02.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation03.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation05.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation07.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation10.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation11.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Lemma02.Symmetrization.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem03.NormwiseBackwardError.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem04.HouseholderQMethod.UnderdeterminedSolve

/-!
# Algorithms.Underdetermined.UnderdeterminedSolve

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): the concrete rounded Householder-QR output is
-- row-wise backward stable under an explicit source-shaped gamma/cond2
-- smallness condition. A legacy coarse Gram predicate is retained below.
--
-- SNE method: solves RᵀRy = b by two rounded triangular solves. The
-- componentwise Gram-system envelope below is only an intermediate result;
-- the source-shaped equation (21.11) endpoint uses the signed factorwise
-- Demmel--Higham cancellation developed in the dedicated Higham21SNE modules.






















namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  QR block algebra for the Q method and SNE setup
-- ============================================================











































































































































































































































































































































































































































































-- Equation (21.7): exact one-parameter first-order expansion.



































































































































































































































































































































































































































































































































































































































































-- Equation (21.7): explicit fixed-radius quadratic remainder bounds.
section Higham21Eq21_7QuadraticRemainder

open Filter
open Asymptotics






























































































































































































































































































































































































































































































set_option maxHeartbeats 5000000























































































































































































































end Higham21Eq21_7QuadraticRemainder


-- ============================================================
-- §21.2  Lemma 21.2 projector/norm bridge
-- ============================================================

























































































































private theorem higham21_rectMatMulVec_matMulRectRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (matMulRectRight A V) x =
      rectMatMulVec A (matMulVec n V x) := by
  simpa [matMulRectRight, rectMatMul, rectMatMulVec, matMulVec] using
    (rectMatMulVec_rectMatMul A V x)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    for the source-oriented construction
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)`, multiplying by the projector source
    vector `x` recovers the first perturbation action `DeltaA1 x`.  This is the
    algebraic step behind `(A + DeltaA)x = (A + DeltaA1)x = b`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x =
      rectMatMulVec DeltaA1 x := by
  let P : Fin n → Fin n → ℝ := lsLemma20_6Projector x
  let Q : Fin n → Fin n → ℝ := lsLemma20_6ProjectorComplement x
  have hP : matMulVec n P x = x := by
    ext j
    simpa [P, matMulVec] using lsLemma20_6Projector_apply_self x hsq j
  have hQ : matMulVec n Q x = 0 := by
    simpa [Q] using lsLemma20_6ProjectorComplement_mulVec_self x hsq
  ext i
  calc
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x i =
        rectMatMulVec
          (fun i j => matMulRectRight DeltaA1 P i j + matMulRectRight DeltaA2 Q i j) x i := by
          unfold rectMatMulVec
          apply Finset.sum_congr rfl
          intro j _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture]
    _ = rectMatMulVec (matMulRectRight DeltaA1 P) x i +
          rectMatMulVec (matMulRectRight DeltaA2 Q) x i := by
          unfold rectMatMulVec
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = rectMatMulVec DeltaA1 (matMulVec n P x) i +
          rectMatMulVec DeltaA2 (matMulVec n Q x) i := by
          rw [congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA1 P x) i,
            congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA2 Q x) i]
    _ = rectMatMulVec DeltaA1 x i := by
          rw [hP, hQ]
          simp [rectMatMulVec]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    system-action form of the previous identity.  The constructed perturbation
    has the same action on `x` as `DeltaA1`, so replacing `DeltaA1` by the
    symmetrized perturbation preserves the equation tested at `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x := by
  have hDelta :=
    higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq
      x hsq DeltaA1 DeltaA2
  ext i
  have hDelta_i := congrFun hDelta i
  unfold rectMatMulVec at hDelta_i ⊢
  calc
    (∑ j : Fin n,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * x j)
        = (∑ j : Fin n, A i j * x j) +
            (∑ j : Fin n, undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j * x j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j : Fin n, A i j * x j) + (∑ j : Fin n, DeltaA1 i j * x j) := by
          rw [hDelta_i]
    _ = ∑ j : Fin n, (A i j + DeltaA1 i j) * x j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the first perturbed system `(A + DeltaA1)x = b` holds, then the
    source-oriented symmetrized perturbation also satisfies `(A + DeltaA)x = b`
    at the same vector `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      b := by
  rw [higham21_lemma21_2_symmetrized_system_mulVec_self_eq A x hsq DeltaA1 DeltaA2]
  exact hDeltaA1




















































private theorem higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector
    {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      DeltaA2 i j +
        matMulRectRight (fun i j => DeltaA1 i j - DeltaA2 i j)
          (lsLemma20_6Projector x) i j := by
  have hmix :=
    higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
      x DeltaA1 DeltaA2 i j
  have hid :
      (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) = DeltaA2 i j := by
    have h := congrFun (congrFun (rectMatMul_id_right DeltaA2) i) j
    simpa [rectMatMul] using h
  rw [hmix]
  unfold matMulRectRight lsLemma20_6ProjectorComplement
  calc
    (∑ k : Fin n, DeltaA1 i k * lsLemma20_6Projector x k j) +
        ∑ k : Fin n, DeltaA2 i k * (idMatrix n k j - lsLemma20_6Projector x k j)
        = ∑ k : Fin n,
            (DeltaA2 i k * idMatrix n k j +
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) +
            ∑ k : Fin n,
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [Finset.sum_add_distrib]
    _ = DeltaA2 i j +
          ∑ k : Fin n,
            (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [hid]

private theorem higham21_matMulRectRight_projector_transpose_mulVec {m n : ℕ}
    (x : Fin n → ℝ) (H : Fin m → Fin n → ℝ) (y : Fin m → ℝ)
    (j : Fin n) :
    rectMatMulVec (finiteTranspose (matMulRectRight H (lsLemma20_6Projector x))) y j =
      ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
  unfold rectMatMulVec finiteTranspose matMulRectRight lsLemma20_6Projector
  calc
    (∑ i : Fin m, (∑ k : Fin n, H i k * (x k * x j / vecNorm2Sq x)) * y i)
        = ∑ i : Fin m, ∑ k : Fin n,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k : Fin n, ∑ i : Fin m,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n,
          (∑ i : Fin m, H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n,
          (x k * (∑ i : Fin m, H i k * y i) / vecNorm2Sq x) * x j := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ((∑ k : Fin n, x k * (∑ i : Fin m, H i k * y i)) /
          vecNorm2Sq x) * x j := by
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.sum_div]
    _ = ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
          rfl

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    transposed-system action of the source-oriented projector construction.
    If `x = (A + DeltaA2)^T y`, then
    `(A + DeltaA)^T y = beta x`, where
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)` and
    `beta = 1 + x^T (DeltaA1 - DeltaA2)^T y / x^T x`.

    This is the algebraic step before the source proof shows `beta ≠ 0` and
    sets the new dual vector to `beta^{-1} y`; it does not prove positivity of
    `beta` or the final minimum-norm symmetrization theorem. -/
theorem higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x) :
    rectMatMulVec
        (finiteTranspose
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)) y =
      fun j : Fin n => undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
  let H : Fin m → Fin n → ℝ := fun i j => DeltaA1 i j - DeltaA2 i j
  ext j
  have hDeltaA2_j := congrFun hDeltaA2 j
  have hcorr :=
    higham21_matMulRectRight_projector_transpose_mulVec x H y j
  unfold rectMatMulVec finiteTranspose at hDeltaA2_j ⊢
  calc
    (∑ i : Fin m,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * y i)
        = (∑ i : Fin m, (A i j + DeltaA2 i j) * y i) +
            ∑ i : Fin m, matMulRectRight H (lsLemma20_6Projector x) i j * y i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector]
          ring
    _ = x j +
          ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
            vecNorm2Sq x) * x j := by
          rw [hDeltaA2_j]
          rw [← hcorr]
          rfl
    _ = undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
          unfold undetLemma21_2Beta H
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conditional rescaling step after the source proof's beta algebra.
    If the source-oriented perturbation preserves the first perturbed system,
    `(A + DeltaA2)^T y = x`, and the beta scalar is nonzero, then the same
    constructed perturbation makes `x` a minimum 2-norm solution of the single
    perturbed rectangular system.

    This is intentionally conditional on `beta ≠ 0`; the source proof's
    perturbation-smallness argument that ensures this condition remains a
    separate open dependency. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hbeta : undetLemma21_2Beta x DeltaA1 DeltaA2 y ≠ 0) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let M : Fin m → Fin n → ℝ :=
    fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j
  let beta : ℝ := undetLemma21_2Beta x DeltaA1 DeltaA2 y
  let ytilde : Fin m → ℝ := fun i => beta⁻¹ * y i
  have hfirst : rectMatMulVec M x = b := by
    simpa [M] using
      higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1
        A x hsq DeltaA1 DeltaA2 b hDeltaA1
  have haction :
      rectMatMulVec (finiteTranspose M) y = fun j : Fin n => beta * x j := by
    simpa [M, beta] using
      higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul
        A x DeltaA1 DeltaA2 y hDeltaA2
  have hytilde_eq : rectTransposeMulVec M ytilde = x := by
    ext j
    have hsmul_j :=
      congrFun (rectMatMulVec_smul (finiteTranspose M) beta⁻¹ y) j
    have haction_j := congrFun haction j
    calc
      rectTransposeMulVec M ytilde j =
          rectMatMulVec (finiteTranspose M) ytilde j := by
            rfl
      _ = beta⁻¹ * rectMatMulVec (finiteTranspose M) y j := by
            change rectMatMulVec (finiteTranspose M) (fun i : Fin m => beta⁻¹ * y i) j =
              beta⁻¹ * rectMatMulVec (finiteTranspose M) y j
            exact hsmul_j
      _ = beta⁻¹ * (beta * x j) := by rw [haction_j]
      _ = x j := by
            rw [← mul_assoc, inv_mul_cancel₀ hbeta, one_mul]
  have hsolve : rectMatMulVec M (rectTransposeMulVec M ytilde) = b := by
    rw [hytilde_eq]
    exact hfirst
  have hmin :=
    higham21_eq21_4_rect_transpose_min_norm_of_solves M b ytilde hsolve
  rwa [hytilde_eq] at hmin




























































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the source proof's scalar beta lower bound.
    If the matrix perturbation argument supplies
    `1 - (rho1 + rho2)/(1 - rho2) <= beta`, then the source smallness condition
    `3 * max rho1 rho2 < 1` gives `beta ≠ 0`, so the conditional rescaling
    theorem applies.

    This isolates the remaining matrix work to proving the displayed lower
    bound from pseudoinverse perturbation estimates. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hbound :
      1 - (rho1 + rho2) / (1 - rho2) ≤
        undetLemma21_2Beta x DeltaA1 DeltaA2 y) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero
    A x DeltaA1 DeltaA2 b y hsq hDeltaA1 hDeltaA2
    (higham21_lemma21_2_scalar_beta_ne_zero_of_bound
      rho1 rho2 (undetLemma21_2Beta x DeltaA1 DeltaA2 y) hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the beta numerator bound.  This replaces the
    previous displayed beta lower-bound hypothesis by the equivalent local
    obligation that the absolute beta numerator is bounded by
    `((rho1 + rho2)/(1 - rho2)) * x^T x`.

    The pseudoinverse perturbation estimate needed to prove this absolute
    numerator bound remains open. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2Sq x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) hsq hinner)





































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a vector-action perturbation bound on the beta
    numerator.  This is one step closer to the source pseudoinverse proof than
    the raw scalar lower-bound hypothesis, but it is still conditional on the
    vector-action estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) haction)




































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from operator and dual-vector norm bounds for the beta
    vector-action estimate.  This isolates the remaining source-specific work
    to proving those bounds from pseudoinverse perturbation theory. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
      x DeltaA1 DeltaA2 y halpha hprod hOp hy)




















/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    dual-vector norm bound.  This leaves the source-specific pseudoinverse
    perturbation work to prove the dual-vector estimate and the final product
    budget. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hprod : (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 (alpha + beta) eta hsq hDeltaA1
    hDeltaA2 hsmall (add_nonneg halpha hbeta) hprod
    (higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds
      DeltaA1 DeltaA2 halpha hbeta hDeltaA1Op hDeltaA2Op)
    hy




























/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    source-shaped dual-vector factor estimate.  The remaining source-specific
    work is to prove `||y||₂ <= eta ||x||₂` with
    `eta <= (1 - rho2)^{-1}` from the pseudoinverse perturbation argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
    hsmall halpha hbeta
    (higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le hbeta_le
      heta_le)
    hDeltaA1Op hDeltaA2Op hy























































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a source-shaped product bound on
    `Bplus * (DeltaA1 - DeltaA2)`.  The remaining perturbation proof is to
    instantiate this product bound for `Bplus = (A + DeltaA2)^+` from the
    source smallness hypotheses. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose B) y = x := by
    simpa [B, y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        B Bplus x (by simpa [B] using hDomainSym) (by simpa [B] using hDomainX)
  have hActionGamma :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        x DeltaA1 DeltaA2 Bplus hgamma hProduct
  have hAction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x :=
    le_trans hActionGamma
      (mul_le_mul_of_nonneg_right hgamma_le (vecNorm2_nonneg x))
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall hAction

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the source-shaped product
    handoff.  Under Gram nonsingularity for `B = A + DeltaA2`, the printed
    hypothesis `x = Bᵀ y` supplies the domain-projection condition, so the
    remaining source perturbation work is reduced to the product bound
    on `B⁺ (DeltaA1 - DeltaA2)`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let Bplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv B
  have hdetB : Matrix.det (rectGram B : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    simpa [B] using hdet
  have hMP : RectMoorePenrosePseudoinverse m n B Bplus :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B hdetB
  have hxRange :
      x = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
    calc
      x = rectTransposeMulVec B y := by
        simpa [B] using hxTranspose
      _ = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
        simpa [Bplus] using
          higham21_lemma21_2_gram_pseudoinverse_range_of_transpose B hdetB y
  have hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x := by
    rw [hxRange]
    simpa [Bplus] using
      higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
        B hdetB (matMulVec m (rectGram B) y)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b Bplus rho1 rho2 gamma hsq hDeltaA1
      (by simpa [B, Bplus] using hMP.domain_projection_symmetric)
      (by simpa [B, Bplus] using hDomainX) hsmall hgamma hgamma_le
      (by simpa [B, Bplus] using hProduct)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing product-bound specialization of the symmetrized minimum-norm
    handoff.  If the perturbed Gram pseudoinverse exists, the printed transpose
    representation `x = (A + DeltaA2)^T y` holds, and the separate operator
    bounds plus the perturbed-pseudoinverse operator bound imply the source
    product budget, then the constructed single perturbation makes `x` the
    minimum 2-norm solution.

    This removes the raw product-bound hypothesis from the concrete Gram route;
    it remains conditional on the perturbed-Gram nonsingularity and
    perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let Bplus : Fin n → Fin m → ℝ :=
    undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j)
  have hgamma : 0 ≤ eta * (alpha + beta) :=
    mul_nonneg heta (add_nonneg halpha hbeta)
  have hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        (eta * (alpha + beta)) := by
    exact
      higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
        DeltaA1 DeltaA2 Bplus heta hDeltaA1Op hDeltaA2Op
        (by simpa [Bplus] using hBplusOp)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 (eta * (alpha + beta))
      hsq hDeltaA1 hdet hxTranspose hsmall hgamma hbudget
      (by simpa [Bplus] using hProduct)




































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse handoff with the scalar product budget derived
    from source-shaped perturbation and pseudoinverse-factor bounds.  The
    remaining matrix perturbation work is still the perturbed Gram
    nonsingularity and the perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
    hdet hxTranspose hsmall halpha hbeta heta
    (higham21_lemma21_2_product_budget_of_source_factor_bounds
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le)
    hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split minimum-norm handoff for the source proof.  If `x = 0`, the
    single perturbation is `DeltaA2`; otherwise the existing projector/beta
    argument applies to the symmetrized perturbation.  The nonzero branch is
    still conditional on the perturbed-Gram nonsingularity and pseudoinverse
    operator estimate that remain the active source-facing gap. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta hbudget hDeltaA1Op
        hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split handoff using source-shaped factor bounds instead of an explicit
    scalar product-budget certificate.  The theorem still exposes the genuine
    nonzero-branch matrix perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta halpha_le hbeta_le
        heta_le hDeltaA1Op hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped case split whose nonzero-branch certificates are only
    required when `x != 0`.  This records that the `x = 0` branch needs only the
    first perturbed equation, while the projector/beta branch still needs the
    perturbed-Gram and pseudoinverse product-budget certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_certificates
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (hbudget : x ≠ 0 →
      eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (hbudget hx) (hDeltaA1Op hx) (hDeltaA2Op hx)
        (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor case split.  The zero branch has no perturbation
    certificates; the nonzero branch derives the scalar product budget from
    source-shaped factor bounds and still exposes only the genuine matrix
    perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (heta_le : x ≠ 0 → eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (halpha_le hx) (hbeta_le hx) (heta_le hx)
        (hDeltaA1Op hx) (hDeltaA2Op hx) (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with the concrete perturbed-pseudoinverse
    operator certificate derived from a perturbed-matrix bound and a Gram-inverse
    bound.  The zero branch still needs only the first perturbed equation; the
    nonzero branch now exposes perturbed Gram nonsingularity and the concrete
    Gram-inverse operator estimate as the remaining matrix-analysis obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta ((sigma + beta) * eta)
    hDeltaA1 hdet hxTranspose hsmall halpha hbeta
    (fun hx => mul_nonneg (add_nonneg (hsigma hx) (hbeta hx)) (heta hx))
    halpha_le hbeta_le hGramFactor_le hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
        A DeltaA2 (hsigma hx) (hbeta hx) (hAOp hx) (hDeltaA2Op hx)
        (hGramInvOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero-branch handoff with perturbed Gram nonsingularity discharged by
    the Chapter 7 absolute infinity-norm contraction condition on the relative
    Gram perturbation.  The remaining explicit matrix-analysis obligation is
    the operator-2 bound for the concrete perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with both perturbed Gram nonsingularity and
    the concrete Gram-inverse operator certificate derived from the Chapter 7
    absolute left-product contraction.  The remaining source-side obligation is
    the scalar factor bound for the explicit Chapter 7 inverse candidate. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma
    (frobNorm
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)))
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma
    (fun _ =>
      frobNorm_nonneg
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))
    halpha_le hbeta_le hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise Gram-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  The componentwise estimate supplies the
    absolute left-product contraction used by the previous theorem. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv rho1 rho2 alpha beta sigma
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    hDeltaA1
    (fun hx =>
      mul_nonneg (hGramEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hGramSmallLt hGramLeftInv
    (fun hx =>
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  A componentwise rectangular bound on
    `DeltaA2` induces the Gram perturbation budget used by the componentwise
    theorem above. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv
    (undetGramPerturbationComponentBudget A E eps)
    rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
    hGramSmallLt hGramLeftInv
    (fun hx =>
      undetGramPerturbationComponentBudget_nonneg A E
        (hDataEpsNonneg hx) (hDataE hx))
    (fun hx =>
      undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
        (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with the Chapter 7 candidate factor
    replaced by a concrete conservative bound from the inverse-candidate
    infinity-norm estimate.  The remaining explicit source obligation is the
    smallness of the induced first product. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E
      rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
      hGramSmallLt hGramLeftInv hDataE hDeltaA2Component hxTranspose
      hsmall halpha hbeta hsigma halpha_le hbeta_le ?_ hAOp
      hDeltaA1Op hDeltaA2Op
  intro hx
  have hGramBound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c := by
    simpa [c, EGram] using
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv EGram eps (hDataEpsNonneg hx)
        (by
          simpa [EGram] using
            undetGramPerturbationComponentBudget_nonneg A E
              (hDataEpsNonneg hx) (hDataE hx))
        (by
          simpa [EGram] using
            undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
              (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
  have hCand :
      frobNorm
          (ch7Problem711PerturbedInverseCandidate m AAT_inv
            (undetGramPerturbation A DeltaA2)) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv (undetGramPerturbation A DeltaA2) c
      (by
        dsimp [c, EGram]
        exact mul_nonneg (hDataEpsNonneg hx)
          (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps))))
      (by simpa [c, EGram] using hGramSmallLt hx) hGramBound
  have hscaled :
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) := by
    simpa [c, EGram] using
      mul_le_mul_of_nonneg_left hCand (add_nonneg (hsigma hx) (hbeta hx))
  exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a sufficient half-radius
    first-product condition.  This replaces the explicit `1 / (1 - c)` factor
    in the previous conservative handoff by the simpler source-facing bound
    using the constant `2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallHalf : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le ?_ hAOp hDeltaA1Op hDeltaA2Op
  · intro hx
    have hhalf : c ≤ (1 / 2 : ℝ) := by
      simpa [c, EGram] using hGramSmallHalf hx
    nlinarith
  · intro hx
    have hc_nn : 0 ≤ c := by
      dsimp [c, EGram]
      exact mul_nonneg (hDataEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
          (undetGramPerturbationComponentBudget A E eps)))
    have hfactor :
        1 / (1 - c) ≤ 2 :=
      higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn
        (by simpa [c, EGram] using hGramSmallHalf hx)
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hinner :
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          (((m : ℝ) * 2) * infNorm AAT_inv) := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor hm_nonneg)
          (infNorm_nonneg AAT_inv)
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
      Real.sqrt_nonneg _
    have hsqrt :
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv) :=
      mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
    have hscaled :
        (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) *
                  (1 /
                    (1 -
                      eps *
                        infNorm
                          (ch7InverseFirstProductSensitivity m AAT_inv
                            (undetGramPerturbationComponentBudget A E eps)))))
                * infNorm AAT_inv)) ≤
          (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) * 2) * infNorm AAT_inv)) := by
      simpa [c, EGram] using
        mul_le_mul_of_nonneg_left hsqrt (add_nonneg (hsigma hx) (hbeta hx))
    exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a source-radius smallness
    condition.  The half-radius first-product condition is discharged from
    `eps <= rhoG` and `rhoG * || |AAT_inv| EGram ||_inf <= 1/2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le hConservativeFactor_le hAOp hDeltaA1Op
      hDeltaA2Op
  intro hx
  have hsens_nonneg :
      0 ≤
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) :=
    infNorm_nonneg _
  exact
    (mul_le_mul_of_nonneg_right (hDataEpsLeRho hx) hsens_nonneg).trans
      (hGramSmallRadius hx)
































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds.  The remaining scalar source obligation is the simplified factor
    involving an upper bound for `sigma + beta` and `||AAT_inv||_inf`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hGramSmallRadius hGramLeftInv
    hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
    halpha_le hbeta_le
    (fun hx =>
      higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
        AAT_inv rho2 sigma beta tau omega (hsigma hx) (hbeta hx)
        (hSigmaBeta_le hx) hAATInv_le hSourceFactor_le)
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds and a source Gram-budget radius certificate.  This wrapper replaces
    the exact induced Gram first-product radius by a larger componentwise source
    Gram budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramBudget_le : x ≠ 0 →
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hGramSourceRadius : x ≠ 0 →
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
        A AAT_inv E EGram eps rhoG (hDataEpsNonneg hx)
        ((hDataEpsNonneg hx).trans (hDataEpsLeRho hx)) (hDataE hx)
        (hGramBudget_le hx) (hGramSourceRadius hx))
    hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
    hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget specialization of the conservative rectangular
    data-perturbation handoff.  The induced Gram budget is bounded internally
    by `undetGramPerturbationRowNormBudget`, leaving only a radius condition for
    that row-norm source budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramRowNormRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationRowNormBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (undetGramPerturbationRowNormBudget A E eps)
    rho1 rho2 alpha beta sigma eps rhoG tau omega
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      undetGramPerturbationComponentBudget_le_rowNormBudget A E
        (hDataEpsNonneg hx) (hDataE hx))
    hGramRowNormRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op
















































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the Chapter 7 radius condition reduced
    to separated infinity-norm scalar bounds. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega gamma : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hRowBudget_le : x ≠ 0 →
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (hRowRadius : x ≠ 0 → rhoG * (omega * gamma) ≤ (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      rhoG tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
      (fun hx =>
        higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
          hm A AAT_inv E eps rhoG omega gamma (hrhoG hx) hAATInv_le
          (hRowBudget_le hx) homega (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
      hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
      hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-budget infinity norm discharged
    from uniform row-norm bounds on `A` and `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega a e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hArow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : x ≠ 0 → 0 ≤ a)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega
    ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx =>
      undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E (hDataEpsNonneg hx) (hArow hx) (hErow hx) (ha hx) (he hx))
    hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall
    halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-norm bounds on `A` and `E`
    discharged from operator-2 certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega sigma e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le A i (hsigma hx) (hAOp hx))
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le E i (he hx) (hEOp hx))
    hsigma he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-norm row-budget handoff with the `DeltaA2` operator certificate
    discharged from the componentwise data perturbation bound and an
    operator-2 certificate for `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha (eps * e) sigma
    eps rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    hEOp he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma halpha_le hEpsE_le hSigmaEpsE_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA2 E
        (hDataEpsNonneg hx) (hDeltaA2Component hx) (hEOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the conservative source scalar factor
    supplied in the simpler quadratic dimension form. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hsigma halpha_le hSigmaEpsE_le hAATInv_le
    (higham21_lemma21_2_source_factor_le_of_quadratic_bound
      m rho2 tau omega hSourceFactor_le)
    hAOp hDeltaA1Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with both perturbation operator certificates
    discharged from componentwise data bounds against the same majorant `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (eps * e) sigma eps
    rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp
    he hEpsE_le_rho2 hRowRadius hGramLeftInv hDataE hDeltaA2Component
    hxTranspose hsmall
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma hEpsE_le_rho1 hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA1 E
        (hDataEpsNonneg hx) (hDeltaA1Component hx) (hEOp hx))





















































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the row-radius scalar obligation
    reduced to the source-sized envelope `2*e*tau`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
      tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
      hEpsE_le_rho1 hEpsE_le_rho2
      (fun hx =>
        higham21_lemma21_2_row_radius_of_source_size_bound m n
          (hDataEpsNonneg hx) (he hx) homega (hrhoG hx) (hSigmaEpsE_le hx)
          (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hsmall hsigma hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separated source-size bounds and a
    flat source-radius product.  This wrapper removes the combined
    `sigma + eps * e <= tau` and nested row-radius certificates from the public
    surface used by the guarded nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le_rho1 hEpsE_le_rho2
    (fun hx =>
      higham21_lemma21_2_row_radius_of_flat_source_product m n
        (hFlatSourceRadius hx))
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hsigma
    (fun hx =>
      higham21_lemma21_2_source_size_bound_of_separate_bounds
        (hSigma_le hx) (hEpsE_le_tauE hx) hSourceSize)
    hAATInv_le hSourceFactor_le hAOp










/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common perturbation-radius bound.
    This replaces the duplicate `eps * e <= rho1` and `eps * e <= rho2`
    obligations by the single source-shaped inequality
    `eps * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp











/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a separate source perturbation-size cap.
    This replaces the direct `eps * e <= min rho1 rho2` obligation by
    `eps * e <= rho` together with `rho <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho : x ≠ 0 → eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_source_radius
        (hEpsE_le_rho hx) hrho_le_min)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp












/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a source product cap for the
    perturbation-size radius.  This replaces `eps * e <= rho` by the branch
    bound `eps <= rhoG`, nonnegativity of `e`, and `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_rho hx))
    hrho_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma
    hSigma_le hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp











/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separate source comparisons from the
    perturbation cap `rho` to the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_rho
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp













































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with branch-wise source product bounds
    against the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho1 : x ≠ 0 → rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : x ≠ 0 → rhoG * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
        (hDataEpsLeRho hx) (he hx)
        (hRhoGE_le_rho1 hx) (hRhoGE_le_rho2 hx))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common `rhoG * e` product-radius
    bound.  This replaces the two branch-wise product-radius obligations by the
    single source-shaped inequality `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common product-radius handoff with the data-perturbation source-size
    obligation also expressed as a `rhoG * e` product bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    (fun hx =>
      higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_tauE hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common `rhoG * e` product-radius and product-size handoff with the
    unperturbed matrix operator envelope written directly as the source-size
    quantity `tauA`.  This is the same dependency chain as the preceding
    wrapper with `sigma = tauA`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 tauA eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA (fun _ => le_rfl) hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with nonnegativity of the radius majorant
    derived from the source perturbation bounds `0 <= eps` and `eps <= rhoG`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
        (hDataEpsNonneg hx) (hDataEpsLeRho hx))
    hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with both radius nonnegativity side
    conditions derived from the source perturbation and operator certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        E hx (hEOp hx))
    hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall htauA
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff for the current nonzero branch.  The
    nonnegativity of both operator radii is derived from the `A` and `E`
    operator-envelope certificates on the active branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        A hx (hAOp hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff with the perturbation-size contribution
    written directly as `rhoG * e`, removing the auxiliary `tauE` envelope. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (rhoG * e) tau omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min (fun _ => le_rfl)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the common product-radius
    condition derived from a source cap `rhoG * e <= rho` and separate
    comparisons of `rho` with the two smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    (fun hx =>
      (hRhoGE_le_rho hx).trans
        (higham21_lemma21_2_source_radius_le_min_of_bounds
          hrho_le_rho1 hrho_le_rho2))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp


































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived from the same source perturbation cap used for the smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n htau homega (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    flat source-radius handoff with nonnegativity of `tau` and `omega`
    derived from the active source-size and inverse-norm certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived directly from the common `rhoG * e <= min rho1 rho2` product
    radius, avoiding an auxiliary source cap `rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_min
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_common_product_radius
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_min hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/common-radius handoff with the source-size envelope
    specialized to the exact quantity `tauA + rhoG * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (tauA + rhoG * e) omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall le_rfl
    hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the inverse source-factor condition
    discharged from a unit source-factor bound in the nonzero branch.  The
    zero branch still uses only the first perturbed equation, as in the printed
    proof's separate `x = 0` case. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_one : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ 1)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
        hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min
        hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le
        (higham21_lemma21_2_source_factor_le_inv_of_unit_bound m
          (higham21_lemma21_2_rho2_nonneg_of_common_product_radius E hx
            (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
            (hRhoGE_le_min hx))
          (hsmall hx) (hSourceFactor_le_one hx))
        hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the source factor supplied in the
    min-radius form.  The source smallness condition converts that min-radius
    bound to the unit source-factor condition consumed by the nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_one_of_min_radius_bound m
        (hsmall hx) (hSourceFactor_le_min hx))
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff specialized to the printed perturbation
    size `eps`, eliminating the auxiliary `rhoG` radius when the source bounds
    are already stated directly in terms of `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps eps tauA omega e
    hDeltaA1 hDataEpsNonneg (fun _ => le_rfl) hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the printed smallness condition
    supplied by a common cap on the two perturbation-product radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le : rho1 ≤ rho)
    (hrho2_le : rho2 ≤ rho)
    (hrho_small : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    (fun _ =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        rho1 rho2 rho hrho1_le hrho2_le hrho_small)
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with global scalar, operator-envelope,
    inverse, componentwise-data, and min-radius source-factor assumptions.
    The only remaining branch-dependent assumption is the nonzero-branch
    transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 (fun _ => hDataEpsNonneg) (fun _ => hEOp)
    (fun _ => hEpsE_le_min) hSourceRadius (fun _ => hGramLeftInv)
    (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose hrho1_le_small
    hrho2_le_small hrhoSmall hAATInv_le (fun _ => hSourceFactor_le_min)
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global min-factor handoff with the printed smallness shape
    `3 * max rho1 rho2 < 1`, avoiding an auxiliary common-smallness radius. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (max rho1 rho2)
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose (le_max_left rho1 rho2) (le_max_right rho1 rho2) hsmall
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/global min-factor handoff with the scalar source-radius
    condition supplied against `max rho1 rho2`.  In the nonzero branch,
    `min rho1 rho2 <= max rho1 rho2` and nonnegativity of the source
    coefficient convert this to the min-radius condition consumed downstream. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · let coeff : ℝ :=
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega
    have htauA : 0 ≤ tauA :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
    have he : 0 ≤ e :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
    have homega : 0 ≤ omega :=
      higham21_lemma21_2_omega_nonneg_of_infNorm_bound AAT_inv
        hAATInv_le
    have hcoeff_nonneg : 0 ≤ coeff := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hsize : 0 ≤ tauA + eps * e :=
        add_nonneg htauA (mul_nonneg hDataEpsNonneg he)
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg htwo hm_nonneg) hn_nonneg)
          hsize)
        homega
    have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
      (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
    have hSourceRadius :
        2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
            min rho1 rho2 ≤
          (1 / 2 : ℝ) := by
      change coeff * min rho1 rho2 ≤ (1 / 2 : ℝ)
      exact
        (mul_le_mul_of_nonneg_left hmin_le_max hcoeff_nonneg).trans
          (by simpa [coeff] using hSourceRadiusMax)
    exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
        hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius
        hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/max-radius handoff with the perturbation-radius and
    source-factor min-radius obligations supplied by one scalar max bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactorMax :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    ((le_max_left (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hSourceRadiusMax hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hAATInv_le
    ((le_max_right (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common-radius version of the printed-smallness/max-radius combined-factor
    handoff.  This packages the two source radii by a single scalar majorant
    `rho`, matching the printed `max` smallness condition more closely while
    keeping the scalar radius and operator-envelope obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have hRadiusFactorMin :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho rho := by
    simpa using hRadiusFactor
  have hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho rho ≤
        (1 / 2 : ℝ) := by
    simpa using hSourceRadius
  have hsmallMax : 3 * max rho rho < 1 := by
    simpa using hsmall
  simpa [min_self, max_self] using
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactorMin hSourceRadiusMax
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmallMax hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    combined-factor handoff with the common radius instantiated by the
    concrete scalar
    `max (eps * e) (2*m^2*(tauA + eps*e)*omega)`.  This removes the auxiliary
    radius parameter from the previous wrapper while keeping the scalar
    smallness, source-radius, operator-envelope, and componentwise-data
    obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (max (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega))
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp le_rfl
    hCombinedSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hCombinedSmall hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with common-smallness and source-factor
    caps separated. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_min_of_cap m
        (hSourceFactor_le_cap hx) hFactorCap_le_rho1 hFactorCap_le_rho2)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-factor-cap handoff with global scalar, operator-envelope, and
    componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
    eps tauA omega e hDeltaA1 (fun _ => hDataEpsNonneg)
    (fun _ => hEOp) (fun _ => hEpsE_le_min) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE)
    (fun _ => hDeltaA1Component) (fun _ => hDeltaA2Component)
    hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun _ => hSourceFactor_le_cap) hFactorCap_le_rho1 hFactorCap_le_rho2
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global source-factor-cap handoff with the cap comparison supplied as a
    single min-radius bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_min_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_min : rhoFactor ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  rcases higham21_lemma21_2_source_cap_le_radii_of_le_min
      hFactorCap_le_min with
    ⟨hFactorCap_le_rho1, hFactorCap_le_rho2⟩
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
      eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
      hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
      hSourceFactor_le_cap hFactorCap_le_rho1 hFactorCap_le_rho2 hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps`-specialized handoff with the source perturbation-radius
    condition supplied as separate bounds for the two perturbation radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_branch_bounds
        (hEpsE_le_rho1 hx) (hEpsE_le_rho2 hx))
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps` handoff with both perturbation radii instantiated by the
    common conservative majorant `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E (eps * e) (eps * e) eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp (fun _ => le_rfl) (fun _ => le_rfl)
    (by simpa using hSourceRadius) hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose
    (fun hx =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        (eps * e) (eps * e) (eps * e) le_rfl le_rfl (hsmall hx))
    hAATInv_le (fun hx => by simpa using hSourceFactor_le_radius hx) hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-style self-radius `eps` handoff with global scalar, operator-envelope,
    and componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e hDeltaA1
    (fun _ => hDataEpsNonneg) (fun _ => hEOp) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose (fun _ => hsmall)
    hAATInv_le (fun _ => hSourceFactor_le_radius) (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the Gram perturbation.  The remaining
    nonzero-branch matrix-analysis obligation is the concrete operator-2 bound
    for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
        hm A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the rectangular perturbation `DeltaA2`.
    The only remaining nonzero-branch matrix-analysis obligation is the
    concrete operator-2 bound for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
        hm A DeltaA2 AAT_inv E eps (hDataEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hDataE hx)
        (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped pseudoinverse handoff for the remaining beta argument.
    If `Bplus` is a perturbed pseudoinverse for `B = A + DeltaA2` whose
    domain projection fixes `x`, and `Bplus` has the source perturbation
    operator bound, then the existing separate-operator bridge proves the
    single-perturbation minimum-norm system.

    The still-open matrix perturbation work is to instantiate the projection
    and operator-bound hypotheses for the concrete `(A + DeltaA2)^+`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x := by
    simpa [y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        (fun i j => A i j + DeltaA2 i j) Bplus x hDomainSym hDomainX
  have hy : vecNorm2 y ≤ eta * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
        Bplus x heta hBplusOp
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
      A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Moore--Penrose specialization of the perturbed-pseudoinverse beta handoff.
    A pseudoinverse certificate supplies the domain-projection symmetry needed
    by the source proof; the remaining open perturbation work is the projection
    fixing `x` and the operator bound for the concrete perturbed pseudoinverse. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (fun i j => A i j + DeltaA2 i j) Bplus)
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    A x DeltaA1 DeltaA2 b Bplus rho1 rho2 alpha beta eta hsq hDeltaA1
    hMP.domain_projection_symmetric hDomainX hsmall halpha hbeta heta
    halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the beta handoff for
    `B = A + DeltaA2`.  Under nonsingularity of `B Bᵀ`, the source table
    `Bᵀ(BBᵀ)⁻¹` supplies the Moore--Penrose certificate used by the previous
    wrapper. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hDomainX :
      rectMatMulVec
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hMP : RectMoorePenrosePseudoinverse m n B (undetAplusOfGramNonsingInv B) :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B (by
      simpa [B] using hdet)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b (undetAplusOfGramNonsingInv B)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hMP
      (by simpa [B] using hDomainX) hsmall halpha hbeta heta
      halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op
      (by simpa [B] using hBplusOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse range specialization of the beta handoff.
    Instead of assuming the domain projection fixes `x` directly, it suffices
    that `x` is explicitly represented as `(A + DeltaA2)^+ yB`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (yB : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxRange :
      x =
        rectMatMulVec
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          yB)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b rho1 rho2 alpha beta eta hsq hDeltaA1 hdet
      ?_ hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  rw [hxRange]
  simpa [B] using
    higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
      B (by simpa [B] using hdet) yB

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped Gram-pseudoinverse range handoff.  The printed hypothesis
    `x = (A + DeltaA2)ᵀ y` supplies the concrete pseudoinverse-range
    representation needed by the beta/minimum-norm argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
      A x DeltaA1 DeltaA2 b (matMulVec m (rectGram B) y)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hdet ?_
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  calc
    x = rectTransposeMulVec B y := by
      simpa [B] using hxTranspose
    _ =
        rectMatMulVec (undetAplusOfGramNonsingInv B)
          (matMulVec m (rectGram B) y) := by
      exact
        higham21_lemma21_2_gram_pseudoinverse_range_of_transpose
          B (by simpa [B] using hdet) y

































































private theorem higham21_right_nonneg_le_sqrt_sq_add_sq
    (a b : ℝ) (hb : 0 ≤ b) :
    b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb_sq : b ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a]
  have hsqrt : Real.sqrt (b ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.sqrt_le_sqrt hb_sq
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using hsqrt






















/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        frobNormRect DeltaA2 ≤
          Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (frobNormRect DeltaA1) (frobNormRect DeltaA2)
        (frobNormRect_nonneg DeltaA2)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frob_bound
        x hsq DeltaA1 DeltaA2




























































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the source-case
    single perturbation.  In the zero branch the perturbation is `DeltaA2`;
    in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        rectRowNorm2 DeltaA2 i ≤
          Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (rectRowNorm2 DeltaA1 i) (rectRowNorm2 DeltaA2 i)
        (rectRowNorm2_nonneg DeltaA2 i)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_row_bound
        x hsq DeltaA1 DeltaA2 i

private theorem higham21_sqrt_sq_add_sq_le_sqrt_two_mul
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha_le : a ≤ c) (hb_le : b ≤ c) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 * c := by
  have ha_sq : a ^ 2 ≤ c ^ 2 := (sq_le_sq₀ ha hc).mpr ha_le
  have hb_sq : b ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hb hc).mpr hb_le
  apply (sq_le_sq₀
    (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hc)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith























/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common row-wise relative-bound corollary for the source-case single
    perturbation.  If both input perturbations are bounded row-by-row by
    `eta * ||A(i,:)||_2`, the constructed single perturbation is bounded
    row-by-row by `sqrt 2 * eta * ||A(i,:)||_2`. -/
theorem higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt 2 * eta * rectRowNorm2 A i := by
  have hrow :=
    higham21_lemma21_2_single_perturbation_row_bound
      x DeltaA1 DeltaA2 i
  have hcommon_nonneg : 0 ≤ eta * rectRowNorm2 A i :=
    mul_nonneg heta (rectRowNorm2_nonneg A i)
  have hsqrt :
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
          rectRowNorm2 DeltaA2 i ^ 2) ≤
        Real.sqrt 2 * (eta * rectRowNorm2 A i) :=
    higham21_sqrt_sq_add_sq_le_sqrt_two_mul
      (rectRowNorm2_nonneg DeltaA1 i)
      (rectRowNorm2_nonneg DeltaA2 i)
      hcommon_nonneg (hDeltaA1 i) (hDeltaA2 i)
  calc
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i
        ≤ Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
            rectRowNorm2 DeltaA2 i ^ 2) := hrow
    _ ≤ Real.sqrt 2 * (eta * rectRowNorm2 A i) := hsqrt
    _ = Real.sqrt 2 * eta * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  by_cases hx : x = 0
  · have hbeta_le : beta ≤ Real.sqrt (alpha ^ 2 + beta ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq alpha beta hbeta
    have hbound :
        rectOpNorm2Le DeltaA2 (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
      rectOpNorm2Le_mono hbeta_le hDeltaA2
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_op_bound
        x hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================




































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    once the Lemma 21.2 single perturbation is known to make `x_hat` a
    minimum-norm solution, common row-wise relative bounds on the two source
    perturbations give a row-wise backward-error witness with factor
    `sqrt 2 * eta`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat (Real.sqrt 2 * eta) :=
  higham21_rowwise_backward_error_bound_witness m n A
    (undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2) b x_hat
    (Real.sqrt 2 * eta)
    (mul_nonneg (Real.sqrt_nonneg 2) heta)
    hmin
    (fun i => by
      simpa [mul_assoc] using
        higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
          x_hat A DeltaA1 DeltaA2 heta hDeltaA1 hDeltaA2 i)





















































































































































































set_option maxHeartbeats 1200000
/-- Higham, 2nd ed., Chapter 21, Lemma 21.2: the minimum-norm core of the
    printed pseudoinverse-product argument.  This separates the source lemma's
    constructed perturbation from the later row-wise backward-error wrapper. -/
theorem higham21_lemma21_2_single_min_norm_of_pseudoinverse_products
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1)
    (hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2)
    (hsmall : 3 * max rho1 rho2 < 1) :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  case pos =>
    have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hFirst
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  case neg =>
    let z : Fin n → ℝ := rectMatMulVec (finiteTranspose A) y
    have hrho1 : 0 ≤ rho1 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA1) hx hProd1
    have hrho2 : 0 ≤ rho2 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA2) hx hProd2
    have hAplusTz :
        rectMatMulVec (finiteTranspose Aplus) z = y := by
      calc
        rectMatMulVec (finiteTranspose Aplus) z =
            rectMatMulVec (finiteTranspose (rectMatMul A Aplus)) y := by
              simpa [z] using
                (higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
                  Aplus A y)
        _ = rectMatMulVec (finiteTranspose (idMatrix m)) y := by
          rw [hRight]
        _ = y := by
          ext i
          simp [rectMatMulVec, finiteTranspose, idMatrix]
    have hDeltaA2T :
        rectMatMulVec (finiteTranspose DeltaA2) y =
          rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z := by
      rw [hAplusTz.symm]
      exact
        higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
          DeltaA2 Aplus z
    have hSecondMat :
        x = rectMatMulVec
          (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y := by
      simpa [rectTransposeMulVec, rectMatMulVec, finiteTranspose] using hSecond
    have hxsum :
        x = fun j =>
          z j +
            rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
      calc
        x = rectMatMulVec
              (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y :=
          hSecondMat
        _ = fun j =>
              rectMatMulVec (finiteTranspose A) y j +
                rectMatMulVec (finiteTranspose DeltaA2) y j := by
              simpa [finiteTranspose] using
                (rectMatMulVec_mat_add
                  (finiteTranspose A) (finiteTranspose DeltaA2) y)
        _ = fun j =>
              z j +
                rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
              rw [hDeltaA2T]
    have hProd2T :
        rectOpNorm2Le (finiteTranspose (rectMatMul Aplus DeltaA2)) rho2 :=
      rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
        (rectMatMul Aplus DeltaA2) hrho2 hProd2
    have hcancel :
        (fun j =>
          x j +
            -rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j) = z := by
      ext j
      have hj := congrFun hxsum j
      linarith
    have htri :=
      vecNorm2_add_le x
        (fun j =>
          -rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z j)
    rw [hcancel, vecNorm2_neg] at htri
    have hlower :
        (1 - rho2) * vecNorm2 z ≤ vecNorm2 x := by
      calc
        (1 - rho2) * vecNorm2 z =
            vecNorm2 z - rho2 * vecNorm2 z := by ring
        _ ≤ vecNorm2 z -
              vecNorm2
                (rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z) :=
            sub_le_sub_left (hProd2T z) _
        _ ≤ vecNorm2 x := (sub_le_iff_le_add).2 htri
    have hden : 0 < 1 - rho2 := by
      have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
      nlinarith
    have hz :
        vecNorm2 z ≤ (1 / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2 z =
            ((1 - rho2) * vecNorm2 z) / (1 - rho2) := by
              field_simp [ne_of_gt hden]
        _ ≤ vecNorm2 x / (1 - rho2) :=
              (div_le_div_iff_of_pos_right hden).2 hlower
        _ = (1 / (1 - rho2)) * vecNorm2 x := by
              simp only [div_eq_mul_inv, one_mul, mul_comm]
    have hProductSub :
        rectOpNorm2Le
          (rectMatMul Aplus (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rho1 + rho2) := by
      rw [rectMatMul_sub_right]
      exact
        rectOpNorm2Le_sub
          (rectMatMul Aplus DeltaA1) (rectMatMul Aplus DeltaA2)
          hProd1 hProd2
    have hActionZ :=
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        z DeltaA1 DeltaA2 Aplus (add_nonneg hrho1 hrho2) hProductSub
    rw [hAplusTz] at hActionZ
    have hAction :
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
          ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
            ≤ (rho1 + rho2) * vecNorm2 z := hActionZ
        _ ≤ (rho1 + rho2) *
              ((1 / (1 - rho2)) * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left hz (add_nonneg hrho1 hrho2)
        _ = ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
            simp [div_eq_mul_inv, mul_assoc]
    have hsq : ¬ vecNorm2Sq x = 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hminSym :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
        A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hFirst hSecondMat.symm
        hsmall hAction
    simpa [undetLemma21_2SinglePerturbation, hx] using hminSym

/-- Direct Lemma 21.2 row-wise handoff from the printed pseudoinverse-product
    smallness condition.  The proof constructs the source symmetrization in
    the nonzero branch and uses the second perturbation in the zero branch. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (rho1 rho2 eta : ℝ)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1)
    (hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2)
    (hsmall : 3 * max rho1 rho2 < 1)
    (heta : 0 ≤ eta)
    (hrow1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hrow2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x (Real.sqrt 2 * eta) := by
  by_cases hx : x = 0
  case pos =>
    have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hFirst
    have hmin :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
          b x := by
      simpa [undetLemma21_2SinglePerturbation, hx] using hzero
    exact
      higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
        A DeltaA1 DeltaA2 b x heta hmin hrow1 hrow2
  case neg =>
    let z : Fin n → ℝ := rectMatMulVec (finiteTranspose A) y
    have hrho1 : 0 ≤ rho1 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA1) hx hProd1
    have hrho2 : 0 ≤ rho2 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA2) hx hProd2
    have hAplusTz :
        rectMatMulVec (finiteTranspose Aplus) z = y := by
      calc
        rectMatMulVec (finiteTranspose Aplus) z =
            rectMatMulVec (finiteTranspose (rectMatMul A Aplus)) y := by
              simpa [z] using
                (higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
                  Aplus A y)
        _ = rectMatMulVec (finiteTranspose (idMatrix m)) y := by
          rw [hRight]
        _ = y := by
          ext i
          simp [rectMatMulVec, finiteTranspose, idMatrix]
    have hDeltaA2T :
        rectMatMulVec (finiteTranspose DeltaA2) y =
          rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z := by
      rw [hAplusTz.symm]
      exact
        higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
          DeltaA2 Aplus z
    have hSecondMat :
        x = rectMatMulVec
          (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y := by
      simpa [rectTransposeMulVec, rectMatMulVec, finiteTranspose] using hSecond
    have hxsum :
        x = fun j =>
          z j +
            rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
      calc
        x = rectMatMulVec
              (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y :=
          hSecondMat
        _ = fun j =>
              rectMatMulVec (finiteTranspose A) y j +
                rectMatMulVec (finiteTranspose DeltaA2) y j := by
              simpa [finiteTranspose] using
                (rectMatMulVec_mat_add
                  (finiteTranspose A) (finiteTranspose DeltaA2) y)
        _ = fun j =>
              z j +
                rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
              rw [hDeltaA2T]
    have hProd2T :
        rectOpNorm2Le (finiteTranspose (rectMatMul Aplus DeltaA2)) rho2 :=
      rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
        (rectMatMul Aplus DeltaA2) hrho2 hProd2
    have hcancel :
        (fun j =>
          x j +
            -rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j) = z := by
      ext j
      have hj := congrFun hxsum j
      linarith
    have htri :=
      vecNorm2_add_le x
        (fun j =>
          -rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z j)
    rw [hcancel, vecNorm2_neg] at htri
    have hlower :
        (1 - rho2) * vecNorm2 z ≤ vecNorm2 x := by
      calc
        (1 - rho2) * vecNorm2 z =
            vecNorm2 z - rho2 * vecNorm2 z := by ring
        _ ≤ vecNorm2 z -
              vecNorm2
                (rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z) :=
            sub_le_sub_left (hProd2T z) _
        _ ≤ vecNorm2 x := (sub_le_iff_le_add).2 htri
    have hden : 0 < 1 - rho2 := by
      have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
      nlinarith
    have hz :
        vecNorm2 z ≤ (1 / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2 z =
            ((1 - rho2) * vecNorm2 z) / (1 - rho2) := by
              field_simp [ne_of_gt hden]
        _ ≤ vecNorm2 x / (1 - rho2) :=
              (div_le_div_iff_of_pos_right hden).2 hlower
        _ = (1 / (1 - rho2)) * vecNorm2 x := by
              simp only [div_eq_mul_inv, one_mul, mul_comm]
    have hProductSub :
        rectOpNorm2Le
          (rectMatMul Aplus (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rho1 + rho2) := by
      rw [rectMatMul_sub_right]
      exact
        rectOpNorm2Le_sub
          (rectMatMul Aplus DeltaA1) (rectMatMul Aplus DeltaA2)
          hProd1 hProd2
    have hActionZ :=
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        z DeltaA1 DeltaA2 Aplus (add_nonneg hrho1 hrho2) hProductSub
    rw [hAplusTz] at hActionZ
    have hAction :
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
          ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
            ≤ (rho1 + rho2) * vecNorm2 z := hActionZ
        _ ≤ (rho1 + rho2) *
              ((1 / (1 - rho2)) * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left hz (add_nonneg hrho1 hrho2)
        _ = ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
            simp [div_eq_mul_inv, mul_assoc]
    have hsq : ¬ vecNorm2Sq x = 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hminSym :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
        A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hFirst hSecondMat.symm
        hsmall hAction
    have hmin :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
          b x := by
      simpa [undetLemma21_2SinglePerturbation, hx] using hminSym
    exact
      higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
        A DeltaA1 DeltaA2 b x heta hmin hrow1 hrow2









/-- Canonical minimum-norm core of Lemma 21.2, with the source smallness
    condition stated using exact operator norms rather than supplied radii. -/
theorem higham21_lemma21_2_single_min_norm_of_exact_product_norms
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall :
      3 * max (higham21Lemma21_2ProductNorm2 A DeltaA1)
          (higham21Lemma21_2ProductNorm2 A DeltaA2) < 1)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let Aplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv A
  let rho1 : ℝ := higham21Lemma21_2ProductNorm2 A DeltaA1
  let rho2 : ℝ := higham21Lemma21_2ProductNorm2 A DeltaA2
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1 := by
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (rectMatMul Aplus DeltaA1)
      (by simp [rho1, higham21Lemma21_2ProductNorm2, Aplus])
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2 := by
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (rectMatMul Aplus DeltaA2)
      (by simp [rho2, higham21Lemma21_2ProductNorm2, Aplus])
  exact
    higham21_lemma21_2_single_min_norm_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x y rho1 rho2 hRight hFirst hSecond
      hProd1 hProd2 (by simpa [rho1, rho2] using hsmall)




















































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 (Kielbasinski--Schwetlick),
    canonical exact-norm formulation.  Full row rank is represented by Gram
    nonsingularity; `m <= n` is retained explicitly from the source statement. -/
theorem higham21_lemma21_2_source_bundle
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (_hmn : m ≤ n)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall :
      3 * max (higham21Lemma21_2ProductNorm2 A DeltaA1)
          (higham21Lemma21_2ProductNorm2 A DeltaA2) < 1) :
    Higham21Lemma21_2SourceBundle A DeltaA1 DeltaA2 b x := by
  have hmin :=
    higham21_lemma21_2_single_min_norm_of_exact_product_norms
      A DeltaA1 DeltaA2 b x y hFirst hSecond hsmall hdet
  obtain ⟨ytilde, hytilde⟩ :=
    RectMinNormSolution.exists_transpose_witness hmin
  refine
    { min_norm := hmin
      transpose_witness := ⟨ytilde, hytilde.symm⟩
      projector_mixture := ?_
      projector_symmetric := ?_
      projector_idempotent := ?_
      projector_sum := ?_
      op2_bound := ?_
      frobenius_bound := ?_ }
  · intro i j
    exact higham21_lemma21_2_single_perturbation_eq_projector_mixture
      x DeltaA1 DeltaA2 i j
  · intro i j
    exact lsLemma20_6Projector_symmetric x i j
  · exact higham21_lemma21_2_projector_idempotent_all x
  · intro i j
    exact lsLemma20_6Projector_add_complement x i j
  · let alpha : ℝ := complexMatrixOp2 (realRectToCMatrix DeltaA1)
    let beta : ℝ := complexMatrixOp2 (realRectToCMatrix DeltaA2)
    have hOp :
        rectOpNorm2Le
          (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
          (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
      higham21_lemma21_2_single_perturbation_op_bound
        x DeltaA1 DeltaA2
        (by
          simpa [alpha] using
            (complexMatrixOp2_nonneg (realRectToCMatrix DeltaA1)))
        (by
          simpa [beta] using
            (complexMatrixOp2_nonneg (realRectToCMatrix DeltaA2)))
        (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          DeltaA1 le_rfl)
        (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          DeltaA2 le_rfl)
    simpa [alpha, beta] using
      (complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
        (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
        (Real.sqrt_nonneg _) hOp)
  · exact higham21_lemma21_2_single_perturbation_frob_bound
      x DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff with a common source radius
    `rho`.  This version matches the printed smallness/radius shape more
    directly than the self-radius wrapper while still leaving the QR/Q-method
    row-bound obligations explicit. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff from entrywise row-relative perturbation
    bounds. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff specialized to the relative componentwise
    data majorant `E = |A|`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    rho eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hRadiusFactor hSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hAATInv_le
    hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff.  The latest
    source-envelope version of Lemma 21.2 supplies the single perturbed
    minimum-norm system, and common row-wise source perturbation bounds then
    package it as the row-wise backward-error predicate used in Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
      hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hCombinedSmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff from entrywise row-relative
    perturbation bounds.  This is a stronger sufficient condition for the
    row-wise hypotheses consumed by Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hCombinedSmall hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff specialized to the relative
    componentwise data majorant `E = |A|`.  The componentwise perturbation
    bounds then supply the row-wise hypotheses directly. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hCombinedSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hCombinedSmall
    hAATInv_le hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================


































































































































































































































































































































set_option maxHeartbeats 800000














































































































set_option maxHeartbeats 2000000















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================




















































































































































































































































/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise backward-error handoff after the triangular solve.  The theorem
    combines the forward-substitution perturbation certificate with the
    existing Lemma 21.2 row-wise witness surface.  The remaining source work is
    exactly the Q-method row-wise assembly: identify the single Lemma 21.2
    perturbation with the perturbed QR-coordinate system and prove the two
    source row bounds. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        (fun i j =>
            A i j +
              undetLemma21_2SinglePerturbation
                (matMulVec (m + k) Q
                  (Fin.append
                    (fl_forwardSub fp m (matTranspose R_hat) b)
                    (0 : Fin k → ℝ)))
                DeltaA1 DeltaA2 i j) =
          finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k)
                (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdet hsingle
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q
      (Fin.append
        (fl_forwardSub fp m (matTranspose R_hat) b)
        (0 : Fin k → ℝ))
  let A_qr : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose
      (matMulRectLeft Q
        (lsQRTallBlock (k := k)
          (fun a b => R_hat a b + DeltaR a b)))
  have hminQR : RectMinNormSolution m (m + k) A_qr b x_hat := by
    simpa [A_qr, x_hat] using hminCond hdet
  have hsingle' :
      (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        = A_qr := by
    simpa [A_qr, x_hat] using hsingle
  have hminSingle :
      RectMinNormSolution m (m + k)
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat := by
    rw [hsingle']
    exact hminQR
  simpa [x_hat] using
    higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
      A DeltaA1 DeltaA2 b x_hat heta hminSingle
      hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free row-wise backward-error handoff after the triangular
    solve.  Compared with
    `higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff`, the
    stronger `gammaValid fp (2*m)` guard discharges the perturbed transpose
    factor nonsingularity side condition. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      ((fun i j =>
          A i j +
            undetLemma21_2SinglePerturbation
              (matMulVec (m + k) Q
                (Fin.append
                  (fl_forwardSub fp m (matTranspose R_hat) b)
                  (0 : Fin k → ℝ)))
              DeltaA1 DeltaA2 i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hrowCond⟩ :=
    higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
      fp A Q hQ R_hat b hdiag hupper hvalid DeltaA1 DeltaA2
      heta hDeltaA1Row hDeltaA2Row
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, fun hsingle => hrowCond hdet hsingle⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    common-perturbation specialization of the row-wise Q-method handoff.
    Taking `DeltaA1 = DeltaA2 = DeltaA` reduces the Lemma 21.2 single
    perturbation equality to the ordinary QR assembly equality
    `A + DeltaA = (Q [R_hat + DeltaR; 0])^T`. -/
theorem higham21_theorem21_4_forwardSub_single_perturbation_rowwise_backward_error_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (DeltaA : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaARow : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      ((fun i j => A i j + DeltaA i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hrowCond⟩ :=
    higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff_of_gammaValid2
      fp A Q hQ R_hat b hdiag hupper hvalid hvalid2
      DeltaA DeltaA heta hDeltaARow hDeltaARow
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hqr
  apply hrowCond
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q
      (Fin.append
        (fl_forwardSub fp m (matTranspose R_hat) b)
        (0 : Fin k → ℝ))
  calc
    (fun i j =>
        A i j +
          undetLemma21_2SinglePerturbation x_hat DeltaA DeltaA i j)
        = (fun i j => A i j + DeltaA i j) := by
          have hsame :=
            higham21_lemma21_2_single_perturbation_same x_hat DeltaA
          ext i j
          rw [congrFun (congrFun hsame i) j]
    _ =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) := hqr





















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































set_option maxHeartbeats 800000





















































































































































































































































































































































set_option maxHeartbeats 800000














































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: the actual rounded Q-method
    output is row-wise backward stable under the exact Lemma 21.2
    condition-number smallness hypothesis. -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_of_cond2_smallness
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hQsmall : Higham21QMethodQhatRadius fp m k < 1)
    (hCondSmall :
      3 *
        (Higham21QMethodRoundedRowwiseCoefficient fp m k *
          Real.sqrt ((m + k : ℕ) : ℝ) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let eta : ℝ := Higham21QMethodRoundedRowwiseCoefficient fp m k
  let Aplus : Fin (m + k) → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let rho : ℝ :=
    eta * Real.sqrt ((m + k : ℕ) : ℝ) * higham21Cond2With A Aplus
  have heta : 0 ≤ eta := by
    exact Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hvalid
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_qmethod_full_row_rank_canonical_right_inverse hdomain
  obtain ⟨Q_inv, DeltaR, y, hleft, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_common_row_bound
      fp A b hm hdomain hvalid hQsmall
  let DeltaA1 : Fin m → Fin (m + k) → ℝ :=
    Higham21QMethodDeltaA1 A Q_inv
      (fun a b => R_hat a b + DeltaR a b)
  let DeltaA2 : Fin m → Fin (m + k) → ℝ :=
    Higham21QMethodDeltaA2 A Q_hat R_hat
  have hrow1' : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i := by
    simpa [DeltaA1, eta, R_hat] using hrow1
  have hrow2' : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i := by
    simpa [DeltaA2, eta, Q_hat, R_hat] using hrow2
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA1 Aplus eta heta hrow1'
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA2 Aplus eta heta hrow2'
  have hsmall : 3 * max rho rho < 1 := by
    simpa [rho, eta, Aplus] using hCondSmall
  exact
    higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x_hat y rho rho eta hRight
      (by simpa [DeltaA1, x_hat, Q_hat, R_hat, y1] using hfirst)
      (by simpa [DeltaA2, x_hat, Q_hat, R_hat, y1] using hsecond)
      hProd1 hProd2 hsmall heta hrow1' hrow2'

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: source-facing rounded Q-method
    stability.  The concrete index realizes the printed
    `gamma_tilde_{mn}`, and `gamma * cond2(A) < 1` is the explicit repository
    form of Higham's stated condition `cond2(A) m n gamma_n < 1`. -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (gamma fp (Higham21QMethodRoundedGammaIndex m k)) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let eta := Higham21QMethodRoundedRowwiseCoefficient fp m k
  let N := m + k
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  let cond := higham21Cond2With A (undetAplusOfGramNonsingInv A)
  have hComputed : gammaValid fp (Higham21QMethodComputedGammaIndex m k) :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hQsmall : Higham21QMethodQhatRadius fp m k < 1 :=
    Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid fp m k hm hvalid
  have heta0 : 0 ≤ eta := by
    exact Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hComputed
  have hetaBase : eta ≤ gamma fp H := by
    simpa [eta, H] using
      Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base fp m k hm hvalid
  have hBaseValid : gammaValid fp H :=
    gammaValid_mono fp (by
      simpa [H] using Higham21QMethodRoundedGammaBaseIndex_le_index m k hm) hvalid
  have hN : 1 ≤ N := by simp [N]; omega
  have hfactor : 1 ≤ 3 * N := by omega
  have hscaled :
      ((3 * N : ℕ) : ℝ) * gamma fp H ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    simpa [Higham21QMethodRoundedGammaIndex, N, H] using
      gamma_nsmul_le fp (3 * N) H hfactor hvalid
  have hscalar :
      3 * eta * Real.sqrt (N : ℝ) ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    calc
      3 * eta * Real.sqrt (N : ℝ) ≤
          3 * gamma fp H * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaBase (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ 3 * gamma fp H * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (higham21_sqrt_nat_le_nat N)
          (mul_nonneg (by norm_num) (gamma_nonneg fp hBaseValid))
      _ = ((3 * N : ℕ) : ℝ) * gamma fp H := by
        push_cast
        ring
      _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) := hscaled
  have hcond0 : 0 ≤ cond := by
    exact higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  have hCondActual :
      3 * (eta * Real.sqrt (N : ℝ) * cond) < 1 := by
    have hle :
        3 * (eta * Real.sqrt (N : ℝ) * cond) ≤
          gamma fp (Higham21QMethodRoundedGammaIndex m k) * cond := by
      calc
        3 * (eta * Real.sqrt (N : ℝ) * cond) =
            (3 * eta * Real.sqrt (N : ℝ)) * cond := by ring
        _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) * cond :=
          mul_le_mul_of_nonneg_right hscalar hcond0
    exact hle.trans_lt (by simpa [cond] using hCondSmall)
  have hraw :
      UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
        (Real.sqrt 2 * eta) := by
    simpa [Q_hat, R_hat, y1, x_hat, eta, N, cond] using
      higham21_theorem21_4_computed_qhat_rowwise_backward_stable_of_cond2_smallness
        fp A b hm hdomain hComputed hQsmall hCondActual
  have hcoeff :
      Real.sqrt 2 * eta ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    simpa [eta] using
      Higham21QMethodRoundedOutputCoefficient_le_gamma_index fp m k hm hvalid
  exact higham21_rowwise_backward_error_bound_mono hraw
    (gamma_nonneg fp hvalid) hcoeff





















































































-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================





























-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================





































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, equation (21.11), concrete Q-method
    composition theorem.

    Theorem 21.4 supplies the actual rounded `Q_hat` output and a rowwise
    perturbation with radius `gamma_tilde_mn`.  Theorem 21.1 supplies the
    orthogonal first-order decomposition.  The result is the exact finite
    relative inequality

    `||x_hat-x||/||x|| <= n*gamma_tilde_mn*cond2(A) + ||R||/||x||`,

    where `R` is the explicit bilinear remainder above.  Consequently a
    quadratic estimate for `R` gives the printed `+ O(u^2)` form without any
    further algorithmic or certificate assumption. -/
theorem higham21_eq21_11_computed_qhat_relative_forward_error_with_remainder
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hk : 0 < k) (hb : b ≠ 0)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    ∃ (DeltaA : Fin m → Fin (m + k) → ℝ) (z_hat : Fin m → ℝ),
      UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta ∧
      rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat = x_hat ∧
      higham21Eq21_11FirstOrder A DeltaA b =
        higham21Eq21_7FirstOrder A DeltaA b (0 : Fin m → ℝ)
          (undetGramNonsingInv A) ∧
      ((fun j => x_hat j - x j) =
        fun j =>
          higham21Eq21_11FirstOrder A DeltaA b j +
            higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) ∧
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x ∧
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) ∧
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
  dsimp only
  let x_hat : Fin (m + k) → ℝ :=
    higham21Eq21_11ComputedQhat fp m k A b
  let Aplus : Fin (m + k) → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let x : Fin (m + k) → ℝ := rectMatMulVec Aplus b
  let eta : ℝ := gamma fp (Higham21QMethodRoundedGammaIndex m k)
  change ∃ (DeltaA : Fin m → Fin (m + k) → ℝ) (z_hat : Fin m → ℝ),
    UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta ∧
      rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat = x_hat ∧
      higham21Eq21_11FirstOrder A DeltaA b =
        higham21Eq21_7FirstOrder A DeltaA b (0 : Fin m → ℝ)
          (undetGramNonsingInv A) ∧
      ((fun j => x_hat j - x j) =
        fun j =>
          higham21Eq21_11FirstOrder A DeltaA b j +
            higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) ∧
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x ∧
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) ∧
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x
  have hcert :
      UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat eta := by
    simpa [x_hat, eta, higham21Eq21_11ComputedQhat] using
      higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
        fp A b hm hdomain hvalid hCondSmall
  rcases hcert with ⟨DeltaA, hfeas⟩
  obtain ⟨z_hat, hrange⟩ := hfeas.min_norm.exists_transpose_witness
  have hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_qmethod_full_row_rank_gram_det_ne_zero hdomain
  have hfirstEq :=
    higham21_eq21_11_firstOrder_eq_eq21_7_firstOrder
      A DeltaA b hdet
  have hexact :=
    higham21_eq21_11_exact_finite_forward_expansion
      A DeltaA b x_hat z_hat hdet hfeas.min_norm.system_eq hrange
  have hN : 2 ≤ m + k := by omega
  have hfirstBound :
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [Aplus, x] using
      higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
        A DeltaA b hN hdet hfeas.eta_nonneg hfeas.row_bound
  have habsolute :
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) := by
    calc
      vecNorm2 (fun j => x_hat j - x j) =
          vecNorm2 (fun j =>
            higham21Eq21_11FirstOrder A DeltaA b j +
              higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) :=
        congrArg vecNorm2 hexact
      _ ≤ vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) +
            vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) :=
        vecNorm2_add_le _ _
      _ ≤ ((m + k : ℕ) : ℝ) * eta *
              higham21Cond2With A Aplus * vecNorm2 x +
            vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) :=
        by nlinarith [hfirstBound]
  have hxmin : RectMinNormSolution m (m + k) A b x := by
    simpa [x, Aplus] using
      higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
        A b hdet
  have hxne : x ≠ 0 := by
    intro hx0
    apply hb
    rw [← hxmin.system_eq, hx0]
    ext i
    simp [rectMatMulVec]
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hxnorm
    apply hxne
    ext j
    exact (vecNorm2_eq_zero_iff x).mp hxnorm j
  have hxnorm_pos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  have hrelative :
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
    calc
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
          (((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus *
                vecNorm2 x +
              vecNorm2
                (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat)) /
            vecNorm2 x :=
        div_le_div_of_nonneg_right habsolute (le_of_lt hxnorm_pos)
      _ = ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
        field_simp [hxnorm_ne]
  exact ⟨DeltaA, z_hat, hfeas, hrange, hfirstEq, hexact,
    hfirstBound, habsolute, hrelative⟩

end NumStability
