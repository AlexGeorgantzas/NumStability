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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.UnderdeterminedSolve
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

/-!
# Source.Higham.Chapter21.Lemma02.Symmetrization.UnderdeterminedSolve

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
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

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing right-projector mixture for the Kielbasinski--Schwetlick
    construction.  The projector acts on the solution vector `x`, as in the
    printed formula `DeltaA = DeltaA1 P + DeltaA2 (I - P)`.  This is the
    constructed perturbation block, not the full minimum-norm symmetrization
    theorem. -/
noncomputable abbrev undetLemma21_2SymmetrizedPerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  finiteTranspose
    (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))

/-- Nonzero vectors have nonzero squared Euclidean norm.  This local helper lets
    the Chapter 21 Lemma 21.2 wrapper branch on the source proof's `x = 0`
    case while feeding the existing nonzero beta/projector route. -/
theorem higham21_vecNorm2Sq_ne_zero_of_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    vecNorm2Sq x ≠ 0 := by
  intro hsq
  apply hx
  ext i
  have hall :
      ∀ j : Fin n, j ∈ (Finset.univ : Finset (Fin n)) →
        x j ^ 2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => x j ^ 2)
        (by intro j _; exact sq_nonneg (x j))).mp
        (by simpa [vecNorm2Sq] using hsq)
  have hxi2 : x i ^ 2 = 0 := hall i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hxi2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-case perturbation.  The proof takes `DeltaA = DeltaA2` when the
    candidate solution `x` is zero; otherwise it uses the right-projector
    mixture already represented by `undetLemma21_2SymmetrizedPerturbation`. -/
noncomputable def undetLemma21_2SinglePerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  if x = 0 then DeltaA2 else undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the transposed Chapter 20 construction is exactly the right-projector
    mixture `DeltaA1 P + DeltaA2 (I - P)` used in the proof. -/
theorem higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
  have hmix :=
    lsLemma20_6Perturbation_eq_projector_mixture
      x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i
  have hrightQ :
      matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i =
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6ProjectorComplement_symmetric x j k]
    ring
  have hrightP :
      matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i =
        matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6Projector_symmetric x j k]
    ring
  calc
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
        lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i := rfl
    _ = matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i +
          matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i := hmix
    _ = matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j +
          matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
          rw [hrightQ, hrightP]
    _ = matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
          matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the two source perturbation slots are the same matrix, then the
    source-case single perturbation collapses back to that matrix. -/
theorem higham21_lemma21_2_single_perturbation_same {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ) :
    undetLemma21_2SinglePerturbation x DeltaA DeltaA = DeltaA := by
  by_cases hx : x = 0
  · simp [undetLemma21_2SinglePerturbation, hx]
  · ext i j
    calc
      undetLemma21_2SinglePerturbation x DeltaA DeltaA i j =
          undetLemma21_2SymmetrizedPerturbation x DeltaA DeltaA i j := by
            simp [undetLemma21_2SinglePerturbation, hx]
      _ =
          matMulRectRight DeltaA (lsLemma20_6Projector x) i j +
            matMulRectRight DeltaA (lsLemma20_6ProjectorComplement x) i j :=
            higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
              x DeltaA DeltaA i j
      _ =
          matMulRectRight DeltaA
            (fun a b => lsLemma20_6Projector x a b +
              lsLemma20_6ProjectorComplement x a b) i j := by
            unfold matMulRectRight
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = matMulRectRight DeltaA (idMatrix n) i j := by
            unfold matMulRectRight
            apply Finset.sum_congr rfl
            intro k _
            simpa using
              congrArg (fun t : ℝ => DeltaA i k * t)
                (lsLemma20_6Projector_add_complement x k j)
      _ = DeltaA i j := by
            have h := congrFun (congrFun (rectMatMul_id_right DeltaA) i) j
            simpa [rectMatMul, matMulRectRight] using h




















































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    zero-vector branch of the Kielbasinski--Schwetlick proof.  If the printed
    candidate `x` is zero, the source proof takes the single perturbation to be
    `DeltaA2`; the first perturbed equation then forces `b = 0`, so the zero
    vector is the minimum 2-norm solution for the `A + DeltaA2` system.

    This is only the `x = 0` branch.  The nonzero branch uses the projector
    mixture and beta argument below. -/
theorem higham21_lemma21_2_zero_branch_min_norm_of_deltaA2 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hx : x = 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x := by
  subst x
  have hb : b = 0 := by
    rw [← hDeltaA1]
    ext i
    simp [rectMatMulVec]
  exact rectMinNormSolution_zero_of_rhs_zero
    (fun i j => A i j + DeltaA2 i j) b hb

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the scalar `beta = 1 + x^T H^T y / x^T x`, where
    `H = DeltaA1 - DeltaA2`, used to rescale the dual vector in the proof. -/
noncomputable def undetLemma21_2Beta {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) : ℝ :=
  1 + (∑ j : Fin n,
    x j * rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y j) /
      vecNorm2Sq x


























































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar smallness adapter for a common bound.  If both perturbation
    products are bounded by `rho`, then `3 * rho < 1` implies the printed
    `3 * max ... < 1` hypothesis. -/
theorem higham21_lemma21_2_three_max_lt_one_of_common_bound
    (a b rho : ℝ)
    (ha : a ≤ rho)
    (hb : b ≤ rho)
    (hrho : 3 * rho < 1) :
    3 * max a b < 1 := by
  have hmax_le : max a b ≤ rho := max_le ha hb
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar endpoint of the source proof's beta-positivity estimate.
    Once the matrix perturbation argument has produced the displayed lower
    bound `beta >= 1 - (a + b)/(1 - b)`, the source smallness condition
    `3 * max a b < 1` implies `beta > 0`.

    This is only the final real-arithmetic step; it does not prove the
    pseudoinverse perturbation lower bound that supplies `hbound`. -/
theorem higham21_lemma21_2_scalar_beta_pos_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    0 < beta := by
  have ha_le : a ≤ max a b := le_max_left a b
  have hb_le : b ≤ max a b := le_max_right a b
  have hden_pos : 0 < 1 - b := by
    nlinarith [hb_le, hsmall]
  have hnum_lt_den : a + b < 1 - b := by
    nlinarith [ha_le, hb_le, hsmall]
  have hfrac_lt_one : (a + b) / (1 - b) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    simpa using hnum_lt_den
  linarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero form of the scalar beta-positivity endpoint. -/
theorem higham21_lemma21_2_scalar_beta_ne_zero_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    beta ≠ 0 :=
  ne_of_gt (higham21_lemma21_2_scalar_beta_pos_of_bound a b beta hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    inner-product route to the source proof's displayed beta lower bound.
    If the numerator `x^T (DeltaA1 - DeltaA2)^T y` is bounded in absolute
    value by `gamma * x^T x`, then
    `beta >= 1 - gamma`.

    This is an algebraic handoff for the still-open pseudoinverse perturbation
    estimate, which must provide the absolute inner-product bound. -/
theorem higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        gamma * vecNorm2Sq x) :
    1 - gamma ≤ undetLemma21_2Beta x DeltaA1 DeltaA2 y := by
  let numer : ℝ :=
    ∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j
  let denom : ℝ := vecNorm2Sq x
  have hden_pos : 0 < denom := by
    exact lt_of_le_of_ne (by simpa [denom] using vecNorm2Sq_nonneg x)
      (by simpa [denom] using hsq.symm)
  have hden_ne : denom ≠ 0 := ne_of_gt hden_pos
  have hinner' : |numer| ≤ gamma * denom := by
    simpa [numer, denom] using hinner
  have hnum_lower : -(gamma * denom) ≤ numer := (abs_le.mp hinner').1
  have hdiv_lower :
      (-(gamma * denom)) / denom ≤ numer / denom :=
    div_le_div_of_nonneg_right hnum_lower (le_of_lt hden_pos)
  have hleft : (-(gamma * denom)) / denom = -gamma := by
    field_simp [hden_ne]
  have hratio_lower : -gamma ≤ numer / denom := by
    simpa [hleft] using hdiv_lower
  have hfinal : 1 - gamma ≤ 1 + numer / denom := by
    linarith
  simpa [undetLemma21_2Beta, numer, denom] using hfinal







































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    vector-action route to the beta numerator bound.  If
    `(DeltaA1 - DeltaA2)^T y` has Euclidean norm at most `gamma * ||x||_2`,
    then Cauchy--Schwarz gives
    `|x^T (DeltaA1 - DeltaA2)^T y| <= gamma * x^T x`.

    The remaining source perturbation work is to supply this vector-action
    bound from pseudoinverse estimates. -/
theorem higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x) :
    |∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j| ≤
      gamma * vecNorm2Sq x := by
  let z : Fin n → ℝ :=
    rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y
  calc
    |∑ j : Fin n, x j * z j|
        ≤ vecNorm2 x * vecNorm2 z :=
            abs_vecInnerProduct_le_vecNorm2_mul x z
    _ ≤ vecNorm2 x * (gamma * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left (by simpa [z] using haction)
              (vecNorm2_nonneg x)
    _ = gamma * vecNorm2Sq x := by
            rw [← vecNorm2_sq x]
            ring

































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator/vector route to the beta vector-action bound.  An operator-2
    bound for `(DeltaA1 - DeltaA2)^T`, together with a bound on the auxiliary
    dual vector `y` in terms of `x`, gives the vector-action estimate needed by
    the beta handoff.

    The source pseudoinverse perturbation argument is still responsible for
    proving the operator and dual-vector bounds used here. -/
theorem higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    {alpha eta gamma : ℝ}
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ gamma)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
      gamma * vecNorm2 x := by
  calc
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
        ≤ alpha * vecNorm2 y := hOp y
    _ ≤ alpha * (eta * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hy halpha
    _ = (alpha * eta) * vecNorm2 x := by ring
    _ ≤ gamma * vecNorm2 x :=
        mul_le_mul_of_nonneg_right hprod (vecNorm2_nonneg x)

































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 triangle step for the remaining beta obligation.  Separate
    operator bounds on `DeltaA1` and `DeltaA2` give an operator bound for
    `(DeltaA1 - DeltaA2)^T`. -/
theorem higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ}
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le
      (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
      (alpha + beta) :=
  rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    (fun i j => DeltaA1 i j - DeltaA2 i j)
    (add_nonneg halpha hbeta)
    (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)





































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar product-budget bridge for the operator/dual-vector route.  If the
    two perturbation operator bounds are no larger than `rho1` and `rho2`, and
    the dual-vector factor is bounded by `(1 - rho2)^{-1}`, then the product
    budget required by the beta handoff follows. -/
theorem higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  have hden_pos : 0 < 1 - rho2 := by
    nlinarith [hrho2_le, hsmall]
  have hsum_le : alpha + beta ≤ rho1 + rho2 :=
    add_le_add halpha_le hbeta_le
  have hsum_rhs_nonneg : 0 ≤ rho1 + rho2 :=
    le_trans (add_nonneg halpha hbeta) hsum_le
  have hprod :
      (alpha + beta) * eta ≤ (rho1 + rho2) * (1 - rho2)⁻¹ :=
    mul_le_mul hsum_le heta_le heta hsum_rhs_nonneg
  simpa [div_eq_mul_inv] using hprod









































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    algebraic action of the perturbed pseudoinverse transpose used in the
    source proof.  Applying `Bᵀ` to `Bplusᵀ x` is the transposed action of the
    domain projection `Bplus B` on `x`. -/
theorem higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      rectMatMulVec (finiteTranspose (rectMatMul Bplus B)) x := by
  ext j
  unfold rectMatMulVec finiteTranspose rectMatMul
  calc
    ∑ i : Fin m, B i j * (∑ k : Fin n, Bplus k i * x k)
        = ∑ i : Fin m, ∑ k : Fin n, B i j * (Bplus k i * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin m, B i j * (Bplus k i * x k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ i : Fin m, Bplus k i * B i j) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the perturbed pseudoinverse domain projection is symmetric and fixes
    `x`, then the source proof's choice `y = Bplusᵀ x` solves
    `Bᵀ y = x`. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ)
    (hDomainSym : IsSymmetricFiniteMatrix (rectMatMul Bplus B))
    (hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      x := by
  rw [higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection]
  have htranspose :
      finiteTranspose (rectMatMul Bplus B) = rectMatMul Bplus B := by
    ext i j
    exact hDomainSym j i
  rw [htranspose, hDomainX]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a perturbation-pseudoinverse operator bound gives the dual-vector estimate
    for the source proof's choice `y = Bplusᵀ x`. -/
theorem higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
    {m n : ℕ}
    (Bplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    {eta : ℝ}
    (heta : 0 ≤ eta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    vecNorm2 (rectMatMulVec (finiteTranspose Bplus) x) ≤ eta * vecNorm2 x :=
  (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Bplus heta hBplusOp) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped product-bound bridge.  A direct operator bound for
    `Bplus * (DeltaA1 - DeltaA2)` gives the vector-action estimate for
    `(DeltaA1 - DeltaA2)ᵀ (Bplusᵀ x)` used in the beta numerator. -/
theorem higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x)) ≤
      gamma * vecNorm2 x := by
  have haction :
      rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x) =
        rectMatMulVec
          (finiteTranspose
            (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)))
          x :=
    higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
      (fun i j => DeltaA1 i j - DeltaA2 i j) Bplus x
  rw [haction]
  exact
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      hgamma hProduct) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete operator-product estimate used in the beta lower-bound route.
    Separate operator-2 bounds for `DeltaA1`, `DeltaA2`, and the perturbed
    pseudoinverse candidate `Bplus` imply an operator bound for the source
    product `Bplus * (DeltaA1 - DeltaA2)`.

    This is the product-bound estimate only; the source perturbation theorem
    must still supply the perturbed-pseudoinverse operator bound. -/
theorem higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
    {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {alpha beta eta : ℝ}
    (heta : 0 ≤ eta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      (eta * (alpha + beta)) :=
  rectOpNorm2Le_rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)
    heta hBplusOp (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)

























































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor budget for the concrete perturbed-pseudoinverse route.
    The printed estimates `alpha <= rho1`, `beta <= rho2`, and
    `eta <= (1 - rho2)^{-1}` imply the product budget in the orientation used
    by the concrete Gram-pseudoinverse handoff. -/
theorem higham21_lemma21_2_product_budget_of_source_factor_bounds
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2) := by
  have hbudget :
      (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) :=
    higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le
  simpa [mul_comm] using hbudget






































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    quadratic source-size scalar bound for the conservative Chapter 7 factor. -/
theorem higham21_lemma21_2_source_factor_le_of_quadratic_bound
    (m : ℕ) (rho2 tau omega : ℝ)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹) :
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega)) ≤
      (1 - rho2)⁻¹ := by
  calc
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega))
        = 2 * (m : ℝ) ^ 2 * tau * omega := by
          rw [higham21_sqrt_nat_cast_mul_self m]
          ring
    _ ≤ (1 - rho2)⁻¹ := hSourceFactor_le













































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Chapter 7 inverse-perturbation handoff for the remaining perturbed Gram
    nonsingularity obligation.  If `AA^T` has a left inverse and the relative
    Gram perturbation `AAT_inv * ((A + DeltaA2)(A + DeltaA2)^T - AA^T)` is a
    strict absolute infinity-norm contraction, then the perturbed Gram matrix
    is nonsingular.

    This is not the full source smallness proof; it replaces the raw
    determinant certificate by the repository's existing Neumann-style
    perturbation condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  let GpertInv : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j) GpertInv :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  have hdetAdd :
      Matrix.det
          ((fun i j => G i j + DeltaG i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    exact
      Matrix.det_ne_zero_of_right_inverse
        (A := ((fun i j => G i j + DeltaG i j) :
          Matrix (Fin m) (Fin m) ℝ))
        (B := (GpertInv : Matrix (Fin m) (Fin m) ℝ))
        (by
          ext i j
          rw [Matrix.mul_apply, Matrix.one_apply]
          exact hRight i j)
  have hmatrix :
      ((fun i j => G i j + DeltaG i j) :
        Matrix (Fin m) (Fin m) ℝ) =
        (rectGram B : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [G, DeltaG, undetGramPerturbation, B]
  rw [hmatrix] at hdetAdd
  simpa [B] using hdetAdd

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Chapter 7 inverse perturbation candidate is a certified right inverse
    for the perturbed Gram matrix under the same absolute left-product
    contraction used for nonsingularity above. -/
theorem higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    IsRightInverse m
      (rectGram (fun i j => A i j + DeltaA2 i j))
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  intro i j
  simpa [G, DeltaG, undetGramPerturbation, B] using hRight i j

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    under the Chapter 7 contraction certificate, the repository
    `nonsingInv` chosen for `(A + DeltaA2)(A + DeltaA2)^T` agrees with the
    explicit inverse-perturbation candidate. -/
theorem higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    undetGramNonsingInv (fun i j => A i j + DeltaA2 i j) =
      ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hRight :
      IsRightInverse m (rectGram B)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)) := by
    simpa [B] using
      higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound
  unfold undetGramNonsingInv
  simpa [B] using
    nonsingInv_eq_of_isRightInverse (rectGram B)
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      hRight

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a concrete operator-2 certificate for the perturbed Gram inverse follows
    from the explicit Chapter 7 candidate and the Frobenius operator bound. -/
theorem higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    rectOpNorm2Le
      (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      (frobNorm
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2))) := by
  rw [
    higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
      hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound]
  exact
    rectOpNorm2Le_of_opNorm2Le_square
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      (opNorm2Le_of_frobNorm_self
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))













/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate, obtained by composing the local Frobenius/infinity bridge with
    the Chapter 7 inverse-candidate infinity-norm estimate. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) := by
  let Gcand : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hInf :
      infNorm Gcand ≤ ((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv := by
    simpa [Gcand] using
      problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound
        m hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  calc
    frobNorm Gcand
        ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) * infNorm Gcand :=
          higham21_frobNorm_le_sqrt_card_sq_mul_infNorm Gcand
    _ ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
          mul_le_mul_of_nonneg_left hInf hsqrt_nonneg

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar half-radius adapter for the conservative Chapter 7 inverse-candidate
    factor. -/
theorem higham21_one_div_one_sub_le_two_of_nonneg_le_half
    {c : ℝ}
    (_hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ)) :
    1 / (1 - c) ≤ 2 := by
  have hden_pos : 0 < 1 - c := by nlinarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate under the sufficient half-radius first-product condition. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_half_radius
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ))
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * 2) * infNorm AAT_inv) := by
  have hc_lt : c < 1 := by nlinarith
  have hbase :
      frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hfactor :
      1 / (1 - c) ≤ 2 :=
    higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn hc_half
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
  exact hbase.trans (mul_le_mul_of_nonneg_left hinner hsqrt_nonneg)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a componentwise Gram-perturbation estimate implies the Chapter 7 absolute
    left-product contraction certificate used for perturbed Gram
    nonsingularity. -/
theorem higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    infNormBound m
      (absMatrix m
        (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
      (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E)) := by
  simpa [infNormBound] using
    ch7_abs_left_product_infNorm_le_of_componentwise_bound
      m AAT_inv (undetGramPerturbation A DeltaA2) E eps heps hE hDeltaG

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise source-shaped route to perturbed Gram nonsingularity.  If the
    relative Gram perturbation is small in the Chapter 7 first-product
    sensitivity bound, then `(A + DeltaA2)(A + DeltaA2)^T` is nonsingular. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    hm A DeltaA2 AAT_inv
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    (mul_nonneg heps
      (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hsmall hLeft
    (higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
      A DeltaA2 AAT_inv E eps heps hE hDeltaG)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise rectangular-perturbation route to perturbed Gram
    nonsingularity.  A bound `|DeltaA2| <= eps * E` induces a componentwise
    Gram perturbation budget, which is then passed to the Chapter 7
    first-product smallness condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i k, 0 ≤ E i k)
    (hDeltaA2 : ∀ i k, |DeltaA2 i k| ≤ eps * E i k) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    hm A DeltaA2 AAT_inv (undetGramPerturbationComponentBudget A E eps)
    eps heps hsmall hLeft
    (undetGramPerturbationComponentBudget_nonneg A E heps hE)
    (undetGramPerturbation_abs_le_componentBudget A DeltaA2 E heps hE hDeltaA2)











































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-budget handoff for the Chapter 7 first-product radius condition.
    If the induced Gram perturbation budget is componentwise bounded by a
    nonnegative source Gram budget, then a radius condition for the source
    budget implies the radius condition for the induced budget. -/
theorem higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (eps rhoG : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hE : ∀ i k, 0 ≤ E i k)
    (hBudget_le :
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hSourceRadius :
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have hBudget_nonneg :
      ∀ i j, 0 ≤ undetGramPerturbationComponentBudget A E eps i j :=
    undetGramPerturbationComponentBudget_nonneg A E heps hE
  have hsens_le :
      infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
        infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) :=
    higham21_ch7_first_product_infNorm_le_of_componentwise_le
      AAT_inv (undetGramPerturbationComponentBudget A E eps) EGram
      hBudget_nonneg hBudget_le
  exact (mul_le_mul_of_nonneg_left hsens_le hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    perturbed Gram-pseudoinverse operator-bound reduction.  Bounds for `A`,
    the second perturbation `DeltaA2`, and the inverse candidate for
    `(A + DeltaA2)(A + DeltaA2)^T` imply the operator bound for the concrete
    table `(A + DeltaA2)^T ((A + DeltaA2)(A + DeltaA2)^T)^{-1}`.

    This does not prove the source perturbation estimate for the Gram inverse;
    it exposes that estimate as the remaining matrix-analysis obligation. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    {sigma beta eta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hA : rectOpNorm2Le A sigma)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hGramInv :
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    rectOpNorm2Le
      (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      ((sigma + beta) * eta) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hB : rectOpNorm2Le B (sigma + beta) := by
    simpa [B] using rectOpNorm2Le_add A DeltaA2 hA hDeltaA2
  exact
    rectOpNorm2Le_undetAplusOfGramNonsingInv_of_bounds
      B (add_nonneg hsigma hbeta) hB (by simpa [B] using hGramInv)






























































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor adapter for the conservative Chapter 7 candidate
    bound.  A bound on `sigma + beta` and a bound on `||AAT_inv||_inf`
    imply the concrete conservative factor inequality consumed by the
    rectangular data handoff. -/
theorem higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho2 sigma beta tau omega : ℝ)
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hSigmaBeta_le : sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹) :
    (sigma + beta) *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
      (1 - rho2)⁻¹ := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hm2_nonneg : 0 ≤ (m : ℝ) * 2 :=
    mul_nonneg hm_nonneg (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  have hinv_nonneg : 0 ≤ infNorm AAT_inv :=
    infNorm_nonneg AAT_inv
  have hconcrete_nonneg :
      0 ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) :=
    mul_nonneg hsqrt_nonneg (mul_nonneg hm2_nonneg hinv_nonneg)
  have htau_nonneg : 0 ≤ tau :=
    (add_nonneg hsigma hbeta).trans hSigmaBeta_le
  have hstep_left :
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) :=
    mul_le_mul_of_nonneg_right hSigmaBeta_le hconcrete_nonneg
  have hinner :
      ((m : ℝ) * 2) * infNorm AAT_inv ≤ ((m : ℝ) * 2) * omega :=
    mul_le_mul_of_nonneg_left hAATInv_le hm2_nonneg
  have hsize :
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega) :=
    mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
  have hstep_right :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) :=
    mul_le_mul_of_nonneg_left hsize htau_nonneg
  exact (hstep_left.trans hstep_right).trans hSourceFactor_le


































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    sufficient row-budget radius certificate from separated infinity-norm
    bounds.  This turns the Chapter 7 first-product smallness condition for
    the row-norm Gram budget into the scalar source obligations
    `‖AAT_inv‖∞ <= omega`, `‖rowBudget‖∞ <= gamma`, and
    `rhoG * (omega * gamma) <= 1/2`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega gamma : ℝ)
    (hrhoG : 0 ≤ rhoG)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRowBudget_le :
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (homega : 0 ≤ omega)
    (hRadius : rhoG * (omega * gamma) ≤ (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  let G : Fin m → Fin m → ℝ := undetGramPerturbationRowNormBudget A E eps
  change rhoG * infNorm (matMul m (absMatrix m AAT_inv) G) ≤ (1 / 2 : ℝ)
  have hprod :
      infNorm (matMul m (absMatrix m AAT_inv) G) ≤ omega * gamma := by
    have hsub : infNorm (matMul m (absMatrix m AAT_inv) G) ≤
        infNorm (absMatrix m AAT_inv) * infNorm G :=
      infNorm_matMul_le hm (absMatrix m AAT_inv) G
    have habs : infNorm (absMatrix m AAT_inv) = infNorm AAT_inv :=
      infNorm_absMatrix hm AAT_inv
    have hmul : infNorm (absMatrix m AAT_inv) * infNorm G ≤ omega * gamma := by
      rw [habs]
      exact mul_le_mul hAATInv_le hRowBudget_le (infNorm_nonneg G) homega
    exact hsub.trans hmul
  exact (mul_le_mul_of_nonneg_left hprod hrhoG).trans hRadius



































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-sized row-norm radius certificate from uniform row-norm bounds on
    `A` and `E`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_row_norm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega a e : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hArow : ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : 0 ≤ a)
    (he : 0 ≤ e)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
      hm A AAT_inv E eps rhoG omega
      ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
      hrhoG hAATInv_le
      (undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E heps hArow hErow ha he)
      homega hRadius































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter.  The source-sized envelope
    `sigma + eps * e <= tau` bounds the row-budget expression
    `sigma*e + e*sigma + eps*e*e` by `2*e*tau`. -/
theorem higham21_lemma21_2_row_radius_of_source_size_bound
    (m n : ℕ) {sigma eps e tau omega rhoG : ℝ}
    (heps : 0 ≤ eps)
    (he : 0 ≤ e)
    (homega : 0 ≤ omega)
    (hrhoG : 0 ≤ rhoG)
    (hSigmaEpsE_le : sigma + eps * e ≤ tau)
    (hSourceRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e)))) ≤
      (1 / 2 : ℝ) := by
  have heps_e_nonneg : 0 ≤ eps * e := mul_nonneg heps he
  have hsigma_le_tau : sigma ≤ tau :=
    (le_add_of_nonneg_right heps_e_nonneg).trans hSigmaEpsE_le
  have hsum : sigma + (sigma + eps * e) ≤ tau + tau :=
    add_le_add hsigma_le_tau hSigmaEpsE_le
  have hrow_term :
      sigma * e + e * sigma + eps * e * e ≤ 2 * e * tau := by
    calc
      sigma * e + e * sigma + eps * e * e
          = e * (sigma + (sigma + eps * e)) := by ring
      _ ≤ e * (tau + tau) := mul_le_mul_of_nonneg_left hsum he
      _ = 2 * e * tau := by ring
  have hn :
      (n : ℝ) * (sigma * e + e * sigma + eps * e * e) ≤
        (n : ℝ) * (2 * e * tau) :=
    mul_le_mul_of_nonneg_left hrow_term (by exact_mod_cast Nat.zero_le n)
  have hm :
      (m : ℝ) *
          ((n : ℝ) * (sigma * e + e * sigma + eps * e * e)) ≤
        (m : ℝ) * ((n : ℝ) * (2 * e * tau)) :=
    mul_le_mul_of_nonneg_left hn (by exact_mod_cast Nat.zero_le m)
  have homega_mul :
      omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e))) ≤
        omega * ((m : ℝ) * ((n : ℝ) * (2 * e * tau))) :=
    mul_le_mul_of_nonneg_left hm homega
  exact (mul_le_mul_of_nonneg_left homega_mul hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-size scalar adapter.  Separate source bounds for the unperturbed
    matrix size and the data perturbation size imply the combined
    `sigma + eps * e <= tau` envelope used by the row-radius handoff. -/
theorem higham21_lemma21_2_source_size_bound_of_separate_bounds
    {sigma eps e tauA tauE tau : ℝ}
    (hSigma_le : sigma ≤ tauA)
    (hEpsE_le : eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau) :
    sigma + eps * e ≤ tau := by
  exact (add_le_add hSigma_le hEpsE_le).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter from the flat source product form to the nested
    product shape consumed by the Chapter 7 first-product handoff. -/
theorem higham21_lemma21_2_row_radius_of_flat_source_product
    (m n : ℕ) {e tau omega rhoG : ℝ}
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
      (1 / 2 : ℝ) := by
  have hshape :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  simpa [hshape] using hSourceRadius
































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common perturbation-radius bound to the two
    separate radius inequalities used by the source-factor handoff. -/
theorem higham21_lemma21_2_epsE_le_radii_of_le_min
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_min : eps * e ≤ min rho1 rho2) :
    eps * e ≤ rho1 ∧ eps * e ≤ rho2 :=
  le_min_iff.mp hEpsE_le_min
































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source perturbation-size cap to the common
    `min rho1 rho2` radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_source_radius
    {eps e rho rho1 rho2 : ℝ}
    (hEpsE_le_rho : eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2) :
    eps * e ≤ min rho1 rho2 :=
  hEpsE_le_rho.trans hrho_le_min





























































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-radius adapter from the branch bound `eps <= rhoG` and a
    source product cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
    {eps rhoG e rho : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho : rhoG * e ≤ rho) :
    eps * e ≤ rho :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho





























































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from separate source radius comparisons to the common
    `min rho1 rho2` comparison. -/
theorem higham21_lemma21_2_source_radius_le_min_of_bounds
    {rho rho1 rho2 : ℝ}
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    rho ≤ min rho1 rho2 :=
  le_min hrho_le_rho1 hrho_le_rho2




























































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from branch-wise `rhoG * e` bounds to the common
    `eps * e <= min rho1 rho2` radius condition. -/
theorem higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
    {eps rhoG e rho1 rho2 : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho1 : rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : rhoG * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho1)
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common `rhoG * e` product-radius bound to the two
    branch-wise product bounds used by the nonzero-branch source handoff. -/
theorem higham21_lemma21_2_rhoGE_le_radii_of_le_min
    {rhoG e rho1 rho2 : ℝ}
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    rhoG * e ≤ rho1 ∧ rhoG * e ≤ rho2 :=
  le_min_iff.mp hRhoGE_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    branch-wise perturbation-radius bounds imply the common min-radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_branch_bounds
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_rho1 : eps * e ≤ rho1)
    (hEpsE_le_rho2 : eps * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min hEpsE_le_rho1 hEpsE_le_rho2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-size adapter from the branch perturbation bound
    `eps <= rhoG` and a product-size cap `rhoG * e <= tauE`. -/
theorem higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
    {eps rhoG e tauE : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_tauE : rhoG * e ≤ tauE) :
    eps * e ≤ tauE :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_tauE

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar nonnegativity adapter for a source radius majorant. -/
theorem higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
    {eps rhoG : ℝ}
    (hEps_nonneg : 0 ≤ eps)
    (hEps_le_rhoG : eps ≤ rhoG) :
    0 ≤ rhoG :=
  hEps_nonneg.trans hEps_le_rhoG

/-- A nonzero finite vector can exist only over a nonempty `Fin` domain. -/
theorem higham21_nonempty_fin_of_vec_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    Nonempty (Fin n) := by
  cases n with
  | zero =>
      exfalso
      exact hx (by funext i; exact Fin.elim0 i)
  | succ n =>
      exact ⟨⟨0, Nat.succ_pos n⟩⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-envelope nonnegativity adapter for the nonzero branch. -/
theorem higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
    {m n : ℕ}
    {x : Fin n → ℝ}
    (E : Fin m → Fin n → ℝ)
    {e : ℝ}
    (hx : x ≠ 0)
    (hEOp : rectOpNorm2Le E e) :
    0 ≤ e := by
  letI : Nonempty (Fin n) := higham21_nonempty_fin_of_vec_ne_zero hx
  exact rectOpNorm2Le_radius_nonneg E hEOp


























































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from a source
    perturbation cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_flat_source_radius_of_product_cap
    (m n : ℕ) {rhoG e rho tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_rho : rhoG * e ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hfactor_nonneg :
      0 ≤ 2 * (m : ℝ) * (n : ℝ) * tau * omega := by
    have h2m : 0 ≤ (2 : ℝ) * (m : ℝ) :=
      mul_nonneg (by norm_num) hm_nonneg
    have h2mn : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) :=
      mul_nonneg h2m hn_nonneg
    have h2mnt : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) * tau :=
      mul_nonneg h2mn htau
    exact mul_nonneg h2mnt homega
  have hmul :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) ≤
        (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho :=
    mul_le_mul_of_nonneg_left hRhoGE_le_rho hfactor_nonneg
  have hleft :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  have hright :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho =
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    ring
  have hflat :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    simpa [hleft, hright] using hmul
  exact hflat.trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from the common
    product-radius bound `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_flat_source_radius_of_common_product_radius
    (m n : ℕ) {rhoG e rho1 rho2 tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) :=
  higham21_lemma21_2_flat_source_radius_of_product_cap
    (rho := min rho1 rho2) m n htau homega hRhoGE_le_min hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source smallness condition bounds the second perturbation radius away
    from one. -/
theorem higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one
    {rho1 rho2 : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1) :
    rho2 < 1 := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the second source radius is nonnegative and below one, then the
    reciprocal factor `(1 - rho2)^{-1}` is at least one. -/
theorem higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one
    {rho2 : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hrho2_lt_one : rho2 < 1) :
    1 ≤ (1 - rho2)⁻¹ := by
  have hden_pos : 0 < 1 - rho2 := by linarith
  have hden_le_one : 1 - rho2 ≤ 1 := by linarith
  exact (one_le_inv₀ hden_pos).2 hden_le_one

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    unit source-factor bound implies the inverse-factor bound once
    `0 <= rho2` and the source smallness condition are known. -/
theorem higham21_lemma21_2_source_factor_le_inv_of_unit_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_one :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ 1) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹ :=
  hSourceFactor_le_one.trans
    (higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one hrho2_nonneg
      (higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one hsmall))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a min-radius source-factor bound implies the unit source-factor bound under
    the source smallness condition. -/
theorem higham21_lemma21_2_source_factor_le_one_of_min_radius_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ 1 := by
  have hmax_lt_one : max rho1 rho2 < 1 := by nlinarith
  have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
    (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
  exact le_of_lt
    (lt_of_le_of_lt (hSourceFactor_le_min.trans hmin_le_max) hmax_lt_one)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source-factor cap to the min-radius source-factor
    bound. -/
theorem higham21_lemma21_2_source_factor_le_min_of_cap
    (m : ℕ) {rho rho1 rho2 tau omega : ℝ}
    (hSourceFactor_le_rho :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2 :=
  hSourceFactor_le_rho.trans
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a min-radius cap comparison to the two branch
    comparisons. -/
theorem higham21_lemma21_2_source_cap_le_radii_of_le_min
    {rho rho1 rho2 : ℝ}
    (hrho_le_min : rho ≤ min rho1 rho2) :
    rho ≤ rho1 ∧ rho ≤ rho2 :=
  ⟨hrho_le_min.trans (min_le_left rho1 rho2),
    hrho_le_min.trans (min_le_right rho1 rho2)⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source-size envelope implies nonnegativity of `tau` on the nonzero
    branch once the operator radii and data perturbation radius are available. -/
theorem higham21_lemma21_2_tau_nonneg_of_source_size
    {m n : ℕ}
    (A E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG tauA tau e : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAOp : rectOpNorm2Le A tauA) :
    0 ≤ tau := by
  have htauA : 0 ≤ tauA :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  exact (add_nonneg htauA (mul_nonneg hrhoG he)).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonnegativity of an inverse-norm majorant follows from the infinity-norm
    certificate. -/
theorem higham21_lemma21_2_omega_nonneg_of_infNorm_bound
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    {omega : ℝ}
    (hAATInv_le : infNorm AAT_inv ≤ omega) :
    0 ≤ omega :=
  (infNorm_nonneg AAT_inv).trans hAATInv_le

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    in the nonzero branch, the common product-radius bound makes `rho2`
    nonnegative because `rhoG` and the operator envelope radius `e` are
    nonnegative. -/
theorem higham21_lemma21_2_rho2_nonneg_of_common_product_radius
    {m n : ℕ}
    (E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG e rho1 rho2 : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    0 ≤ rho2 := by
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hprod_nonneg : 0 ≤ rhoG * e := mul_nonneg hrhoG he
  exact hprod_nonneg.trans (hRhoGE_le_min.trans (min_le_right rho1 rho2))


































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Frobenius-squared norm bound for the projector mixture used to replace
    two perturbation blocks by one. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  have h :=
    lsLemma20_6Perturbation_frobNormSqRect_le
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormSqRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed bound
    `||Delta A||_F <= (||Delta A_1||_F^2 + ||Delta A_2||_F^2)^(1/2)` for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  have h :=
    lsLemma20_6Perturbation_norm_bound_two_frob
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed bound for the projector mixture.  If
    the two original perturbation blocks have operator-2 bounds `alpha` and
    `beta`, then the constructed perturbation has bound
    `(alpha^2 + beta^2)^(1/2)`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  have hDeltaA2T : rectOpNorm2Le (finiteTranspose DeltaA2) beta :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA2 hbeta hDeltaA2
  have hDeltaA1T : rectOpNorm2Le (finiteTranspose DeltaA1) alpha :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA1 halpha hDeltaA1
  have hbase :
      rectOpNorm2Le
        (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    lsLemma20_6Perturbation_norm_bound_two_operator
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
      hbeta halpha hDeltaA2T hDeltaA1T
  have htrans :
      rectOpNorm2Le
        (finiteTranspose
          (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
      (Real.sqrt_nonneg _) hbase
  have hrad : beta ^ 2 + alpha ^ 2 = alpha ^ 2 + beta ^ 2 := by ring
  simpa [undetLemma21_2SymmetrizedPerturbation, hrad] using htrans









/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared Frobenius-norm form of the printed perturbation bound for the
    source-case single perturbation.  In the zero branch the perturbation is
    `DeltaA2`; in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  by_cases hx : x = 0
  · have hD1 : 0 ≤ frobNormSqRect DeltaA1 := frobNormSqRect_nonneg DeltaA1
    have hbound :
        frobNormSqRect DeltaA2 ≤ frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
      nlinarith
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le
        x hsq DeltaA1 DeltaA2























/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared row-wise 2-norm form of the printed perturbation bound for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) ≤
      vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
  let C1 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA2 i j
  let C2 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA1 i j
  have hbase :=
    lsLemma20_6Perturbation_frobNormSqRect_le x hsq C1 C2
  have hleft :
      frobNormSqRect (lsLemma20_6Perturbation x C1 C2) =
        vecNorm2Sq
          (fun j : Fin n =>
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1, C2,
      undetLemma21_2SymmetrizedPerturbation, lsLemma20_6Perturbation,
      finiteTranspose, matMulRectLeft]
  have hC1 :
      frobNormSqRect C1 =
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1]
  have hC2 :
      frobNormSqRect C2 =
        vecNorm2Sq (fun j : Fin n => DeltaA1 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C2]
  calc
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
        = frobNormSqRect (lsLemma20_6Perturbation x C1 C2) := hleft.symm
    _ ≤ frobNormSqRect C1 + frobNormSqRect C2 := hbase
    _ = vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
          rw [hC1, hC2]
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the projector
    mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  apply (sq_le_sq₀
    (rectRowNorm2_nonneg
      (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simpa [rectRowNorm2, vecNorm2_sq] using
    higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le
      x hsq DeltaA1 DeltaA2 i
























































































































-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================




































































































































































































































































theorem higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds_nat_factor
    {m n : ℕ}
    (A Delta : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hrow : ∀ i : Fin m,
      rectRowNorm2 Delta i ≤ eta * rectRowNorm2 A i) :
    rectOpNorm2Le (rectMatMul Aplus Delta)
      (eta * (n : ℝ) * higham21Cond2With A Aplus) := by
  apply rectOpNorm2Le_mono
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (higham21_sqrt_nat_le_nat n) heta)
      (higham21Cond2With_nonneg A Aplus))
  exact
    higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
      A Delta Aplus eta heta hrow

set_option maxHeartbeats 1200000


























































































































































































































































































































































/-- The exact operator-2 norm of the source product `A^+ DeltaA` appearing in
    the smallness hypothesis of Lemma 21.2. -/
noncomputable def higham21Lemma21_2ProductNorm2 {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) : ℝ :=
  complexMatrixOp2
    (realRectToCMatrix
      (rectMatMul (undetAplusOfGramNonsingInv A) DeltaA))








































/-- The source-case perturbation is literally
    `DeltaA1 G1 + DeltaA2 G2`, with `G1 = xx^T/(x^T x)` and `G2 = I-G1`.
    In the zero branch this reads `G1=0`, `G2=I`, and `DeltaA=DeltaA2`. -/
theorem higham21_lemma21_2_single_perturbation_eq_projector_mixture
    {m n : ℕ} (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
  by_cases hx : x = 0
  · subst x
    have hP :
        lsLemma20_6Projector (0 : Fin n → ℝ) =
          (0 : Fin n → Fin n → ℝ) := by
      ext a c
      simp [lsLemma20_6Projector]
    have hQ :
        lsLemma20_6ProjectorComplement (0 : Fin n → ℝ) =
          idMatrix n := by
      ext a c
      simp [lsLemma20_6ProjectorComplement, hP]
    have hid : matMulRectRight DeltaA2 (idMatrix n) i j = DeltaA2 i j := by
      have h := congrFun (congrFun (rectMatMul_id_right DeltaA2) i) j
      simpa [rectMatMul, matMulRectRight] using h
    simp only [undetLemma21_2SinglePerturbation, hP, hQ, hid]
    simp [matMulRectRight]
  · simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
        x DeltaA1 DeltaA2 i j

/-- The rank-one source projector is idempotent also in the `x=0` branch. -/
theorem higham21_lemma21_2_projector_idempotent_all {n : ℕ}
    (x : Fin n → ℝ) :
    matMul n (lsLemma20_6Projector x) (lsLemma20_6Projector x) =
      lsLemma20_6Projector x := by
  by_cases hx : x = 0
  · subst x
    ext i j
    simp [matMul, lsLemma20_6Projector]
  · exact lsLemma20_6Projector_idempotent x
      (higham21_vecNorm2Sq_ne_zero_of_ne_zero hx)

/-- A source-facing bundle for Higham's Lemma 21.2.  It records the explicit
    projector construction, an exact transpose witness, minimum-norm recovery,
    and the printed `p=2` and Frobenius square-sum norm bounds. -/
structure Higham21Lemma21_2SourceBundle {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop where
  min_norm :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x
  transpose_witness : ∃ dual : Fin m → ℝ,
    x = rectTransposeMulVec
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
        dual
  projector_mixture : ∀ i j,
    undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j
  projector_symmetric :
    IsSymmetricFiniteMatrix (lsLemma20_6Projector x)
  projector_idempotent :
    matMul n (lsLemma20_6Projector x) (lsLemma20_6Projector x) =
      lsLemma20_6Projector x
  projector_sum : ∀ i j,
    lsLemma20_6Projector x i j +
      lsLemma20_6ProjectorComplement x i j = idMatrix n i j
  op2_bound :
    complexMatrixOp2
        (realRectToCMatrix
          (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)) ≤
      Real.sqrt
        (complexMatrixOp2 (realRectToCMatrix DeltaA1) ^ 2 +
          complexMatrixOp2 (realRectToCMatrix DeltaA2) ^ 2)
  frobenius_bound :
    frobNormRect
        (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2)















































































































































































































































































































































































-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================


































































































































































































































































































































set_option maxHeartbeats 800000














































































































set_option maxHeartbeats 2000000















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































set_option maxHeartbeats 800000





















































































































































































































































































































































set_option maxHeartbeats 800000













































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================





























-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================






































































































































































































































































































































































































































































































































































































































































































end NumStability
