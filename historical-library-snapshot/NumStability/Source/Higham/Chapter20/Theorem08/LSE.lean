import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.GQR
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 20 — LSE

Canonical source correspondence module extracted without change from LSE.
-/

/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced Higham residual for the perturbed `AP` least-squares problem is
    orthogonal to every reduced column whenever it comes from an exact
    perturbed LSE minimizer and a perturbed feasible base point. -/
theorem theorem20_8AP_perturbed_reduced_higham_residual_orthogonal_of_lse_minimizer
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bpertplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x0 y : Fin n → ℝ) (s : Fin m → ℝ)
    (hright :
      rectMatMul (fun i j => B i j + DeltaB i j) Bpertplus =
        idMatrix p)
    (hx0 : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) x0)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hs :
      s =
        fun i =>
          b i + Deltab i -
            rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
            rectMatMulVec
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) Bpertplus)
              (fun j => y j - x0 j) i) :
    ∀ j : Fin n,
      ∑ i : Fin m,
        theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) Bpertplus i j *
          s i = 0 := by
  have hred :
      IsLeastSquaresMinimizer
        (theorem20_8AP (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) Bpertplus)
        (fun i =>
          b i + Deltab i -
            rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
        (fun j => y j - x0 j) :=
    theorem20_8AP_perturbed_unconstrained_minimizer_of_lse_minimizer
      A DeltaA b Deltab B DeltaB Bpertplus d Deltad x0 y hright hx0 hy
  exact
    IsLeastSquaresMinimizer.higham_residual_orthogonal
      (A := theorem20_8AP (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) Bpertplus)
      (b := fun i =>
        b i + Deltab i -
          rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
      (x := fun j => y j - x0 j) (s := s)
      hred (by simpa [lsResidualHigham] using hs)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    Wedin residual-side bound for source and perturbed LSE problems after
    reducing each problem to supplied homogeneous-nullspace coordinates.

This is a reduced-coordinate bridge for the Eldén--Cox--Higham route.  It
uses exact optimality of the source and perturbed constrained problems to
obtain the two reduced least-squares minimizers, then applies the minimizer
form of Wedin's Theorem 20.1 residual estimate. -/
theorem theorem20_8_nullspace_reduced_wedinResidualRHS_le_of_lse_minimizers
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r s : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : r = lsResidualHigham A b x)
    (hs : s = lsResidualHigham
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) y)
    (hrpos : 0 < vecNorm2 r)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => s i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus)) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 r ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  let Ared : Fin m → Fin (k + 1) → ℝ := rectMatMul A N
  let Bred : Fin m → Fin (k + 1) → ℝ :=
    rectMatMul (fun i j => A i j + DeltaA i j) Npert
  let DeltaAred : Fin m → Fin (k + 1) → ℝ :=
    fun i j => Bred i j - Ared i j
  have hxred :
      IsLeastSquaresMinimizer Ared r (0 : Fin (k + 1) → ℝ) := by
    have hraw :
        IsLeastSquaresMinimizer (rectMatMul A N) (lsResidualHigham A b x)
          (0 : Fin (k + 1) → ℝ) :=
      IsLSEMinimizer.reduced_nullspace_minimizer A b B d x N hx hN
    simpa [Ared, hr] using hraw
  have hyred_s :
      IsLeastSquaresMinimizer Bred s (0 : Fin (k + 1) → ℝ) := by
    have hraw :
        IsLeastSquaresMinimizer
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
          (lsResidualHigham (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i) y)
          (0 : Fin (k + 1) → ℝ) :=
      IsLSEMinimizer.reduced_nullspace_minimizer
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) (fun i => d i + Deltad i)
        y Npert hy hNpert
    simpa [Bred, hs] using hraw
  have hyred :
      IsLeastSquaresMinimizer Bred (fun i => r i + (s i - r i))
        (0 : Fin (k + 1) → ℝ) := by
    have hbrhs : (fun i : Fin m => r i + (s i - r i)) = s := by
      ext i
      ring
    simpa [hbrhs] using hyred_s
  have hBred_eq : Bred = fun i j => Ared i j + DeltaAred i j := by
    ext i j
    simp [DeltaAred]
  have hrRed :
      r = fun i => r i - rectMatMulVec Ared (0 : Fin (k + 1) → ℝ) i := by
    ext i
    simp [rectMatMulVec]
  have hsRed :
      s =
        fun i =>
          (r i + (s i - r i)) -
            rectMatMulVec Bred (0 : Fin (k + 1) → ℝ) i := by
    ext i
    simp [rectMatMulVec]
  exact
    IsLeastSquaresMinimizer.wedin_residualRelativeRHS_le_of_min_surface_geometry_source_minimizer
      hm Ared Bred AredPlus BredPlus DeltaAred r (fun i => s i - r i) r s
      (0 : Fin (k + 1) → ℝ) (0 : Fin (k + 1) → ℝ)
      hxred hyred hrpos hAredPlus_pos hAred_norm_nonneg heps_nonneg
      hkappa hdelta hsmall hAredPlus
      (by simpa [Ared, Bred, DeltaAred] using hDelta)
      (by simpa [Ared, Bred, DeltaAred] using hDeltaAred)
      hDeltabred hDeltaAred_norm_budget hDeltabred_norm_budget
      (by simpa [Ared] using hleftA)
      (by simpa [Bred] using hleftB)
      (by simpa [Ared] using hSymA)
      (by simpa [Bred] using hSymB)
      hBred_eq hrRed hsRed
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    projected-action first-order solution bound whose reduced residual estimate
    is supplied by Wedin's Theorem 20.1 on explicit source and perturbed
    homogeneous-nullspace coordinate bases.

The theorem deliberately keeps the concrete nullspace bases, reduced
pseudoinverses, reduced perturbation budgets, projected-action identity, and
scalar residual-amplifier comparison on the surface. -/
theorem
    theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_projected_action_op2_le
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hscale :
      complexMatrixOp2 (realRectToCMatrix APplus) *
          (wedinTheorem20_1ResidualRelativeRHS kappa eps * vecNorm2 r) ≤
        eps * theorem20_8ResidualAmplifier A B APplus
            (theorem20_8BAplus A B Bplus APplus) *
          (vecNorm2 r / frobNormRect A)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
        (theorem20_8BAplus A B Bplus APplus) := by
  have hrelative :
      vecNorm2 (fun i : Fin m => r i - rHigh i) / vecNorm2 r ≤
        wedinTheorem20_1ResidualRelativeRHS kappa eps := by
    have hdelta_rhs :
        vecNorm2 (fun i : Fin m => rHigh i - r i) ≤ Deltabred_norm :=
      hDeltabred
    have hwedin :=
      theorem20_8_nullspace_reduced_wedinResidualRHS_le_of_lse_minimizers
        hm A DeltaA b Deltab B DeltaB d Deltad N Npert AredPlus BredPlus
        x y r rHigh hx hy hN hNpert hr.symm hres.symm hrpos
        hAredPlus_pos hAred_norm_nonneg heps_nonneg hkappa hdelta hsmall
        hAredPlus hDelta hDeltaAred hdelta_rhs hDeltaAred_norm_budget
        hDeltabred_norm_budget hleftA hleftB hSymA hSymB
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hwedin
  exact
    theorem20_8_solution_difference_relative_le_firstOrderRHS_of_wedinResidualRHS_projected_action_op2_le
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y r rHigh
      heps_nonneg hApos hbpos hBpos hdpos hxpos hyx hrpos hmax hAPaction
      hx.1 hy.1 hr hres hrelative hscale
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nullspace-coordinate Wedin route with the residual-amplifier comparison
    reduced to the first-order coefficient inequality. -/
theorem
    theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_first_order_coeff_projected_action_op2_le
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hcoeff :
      complexMatrixOp2 (realRectToCMatrix APplus) * (1 + 2 * kappa) ≤
        theorem20_8ResidualAmplifier A B APplus
            (theorem20_8BAplus A B Bplus APplus) /
          frobNormRect A) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
        (theorem20_8BAplus A B Bplus APplus) :=
  theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_projected_action_op2_le
    hm A DeltaA b Deltab B DeltaB Bplus APplus d Deltad N Npert
    AredPlus BredPlus x y r rHigh heps_nonneg hApos hbpos hBpos hdpos
    hxpos hyx hrpos hmax hAPaction hx hy hN hNpert hr hres
    hAredPlus_pos hAred_norm_nonneg hkappa hdelta hsmall hAredPlus
    hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
    hDeltabred_norm_budget hleftA hleftB hSymA hSymB
    (theorem20_8_wedinResidualRHS_scaled_residual_le_of_first_order_coeff_le
      A B APplus (theorem20_8BAplus A B Bplus APplus) r heps_nonneg hcoeff)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nullspace-coordinate Wedin route with the scalar residual-amplifier
    comparison reduced to the `kappa_B(A)` bracket inequality. -/
theorem
    theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_projected_action_op2_le
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B Bplus APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
        (theorem20_8BAplus A B Bplus APplus) :=
  theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_first_order_coeff_projected_action_op2_le
    hm A DeltaA b Deltab B DeltaB Bplus APplus d Deltad N Npert
    AredPlus BredPlus x y r rHigh heps_nonneg hApos hbpos hBpos hdpos
    hxpos hyx hrpos hmax hAPaction hx hy hN hNpert hr hres
    hAredPlus_pos hAred_norm_nonneg hkappa hdelta hsmall hAredPlus
    hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
    hDeltabred_norm_budget hleftA hleftB hSymA hSymB
    (theorem20_8_wedinResidualRHS_first_order_coeff_le_of_kappaB_bracket
      A B APplus (theorem20_8BAplus A B Bplus APplus) hApos hkappaB
      hbracket)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nullspace-coordinate Wedin route with `kappa_B(A)` bracket scalar
    reduction, packaged in the source-shaped first-order plus explicit
    `eps^2`-coefficient form. -/
theorem
    theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_projected_action_op2_le
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B Bplus APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
          (theorem20_8BAplus A B Bplus APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x r APplus
            (theorem20_8BAplus A B Bplus APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  let BAplus := theorem20_8BAplus A B Bplus APplus
  have hbase :=
    theorem20_8_solution_difference_relative_le_firstOrderRHS_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_projected_action_op2_le
      hm A DeltaA b Deltab B DeltaB Bplus APplus d Deltad N Npert
      AredPlus BredPlus x y r rHigh heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hAPaction hx hy hN hNpert hr hres
      hAredPlus_pos hAred_norm_nonneg hkappa hkappaB hdelta hsmall
      hAredPlus hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
      hDeltabred_norm_budget hleftA hleftB hSymA hSymB hbracket
  have hquad_nonneg :
      0 ≤
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
          (complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
    have hfirst :
        0 ≤ theorem20_8FirstOrderRHS A b B d x r APplus BAplus :=
      theorem20_8FirstOrderRHS_nonneg A b B d x r APplus BAplus
        hApos hBpos hxpos
    have hcoef :
        0 ≤ complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
          complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A := by
      exact add_nonneg
        (mul_nonneg (complexMatrixOp2_nonneg (realRectToCMatrix BAplus))
          (frobNormRect_nonneg B))
        (mul_nonneg (complexMatrixOp2_nonneg (realRectToCMatrix APplus))
          (frobNormRect_nonneg A))
    exact mul_nonneg (mul_nonneg (sq_nonneg eps) hfirst) hcoef
  exact hbase.trans (le_add_of_nonneg_right (by simpa [BAplus] using hquad_nonneg))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nullspace-coordinate Wedin route with the projected-action identity derived
    from the source-style `(AP)^+ AP` left-inverse condition on
    `null(B)`. -/
theorem
    theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_AP_left_inverse_on_nullspace
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B Bplus APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
          (theorem20_8BAplus A B Bplus APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x r APplus
            (theorem20_8BAplus A B Bplus APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) :=
    theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
      A B Bplus APplus hright hAPleft_null (fun k => y k - x k)
  exact
    theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_projected_action_op2_le
      hm A DeltaA b Deltab B DeltaB Bplus APplus d Deltad N Npert
      AredPlus BredPlus x y r rHigh heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hAPaction hx hy hN hNpert hr hres
      hAredPlus_pos hAred_norm_nonneg hkappa hkappaB hdelta hsmall
      hAredPlus hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
      hDeltabred_norm_budget hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated reduced residual orthogonality for the
    perturbed `AP` least-squares problem obtained from a perturbed LSE
    minimizer. -/
theorem
    LSEFullRowRank.theorem20_8AP_perturbed_reduced_higham_residual_orthogonal_of_lse_minimizer
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (d Deltad : Fin p → ℝ) (x0 y : Fin n → ℝ) (s : Fin m → ℝ)
    (hx0 : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) x0)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hs :
      s =
        fun i =>
          b i + Deltab i -
            rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
            rectMatMulVec
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun j => y j - x0 j) i) :
    ∀ j : Fin n,
      ∑ i : Fin m,
        theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
          s i = 0 :=
  _root_.NumStability.theorem20_8AP_perturbed_reduced_higham_residual_orthogonal_of_lse_minimizer
    A DeltaA b Deltab B DeltaB hBpert.rightInverse d Deltad x0 y s
    hBpert.rightInverse_spec hx0 hy hs
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-stacked-full-column-rank nullspace-Wedin route for the
    Moore--Penrose/transpose-range `(AP)^+` certificate.  This derives the
    projected-action side from the printed rank conditions plus the
    rank-tolerant Moore--Penrose certificate, while keeping the reduced
    nullspace bases, Wedin budgets, `kappa_B` identification, and bracket
    inequality explicit. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 r)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred : vecNorm2 (fun i => rHigh i - r i) ≤ Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget : Deltabred_norm ≤ eps * vecNorm2 r)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus
          (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x r APplus
            (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  exact
    _root_.NumStability.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_AP_left_inverse_on_nullspace
      hm A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad
      N Npert AredPlus BredPlus x y r rHigh heps_nonneg hApos hbpos
      hBpos hdpos hxpos hyx hrpos hmax hB.rightInverse_spec
      (LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_lseStackedFullColumnRank
        A hB APplus hMP hBAPt hstack)
      hx hy hN hNpert hr hres hAredPlus_pos hAred_norm_nonneg
      hkappa hkappaB hdelta hsmall hAredPlus hDelta hDeltaAred
      hDeltabred hDeltaAred_norm_budget hDeltabred_norm_budget
      hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-residual specialization of the MP/transpose-range nullspace-Wedin
    route.  This wrapper uses the actual source and perturbed Higham residuals
    directly, removing the caller-facing residual-vector equality witnesses
    while preserving the concrete reduced-coordinate and scalar bracket
    obligations. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residuals
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {delta AredPlus_norm DeltaAred_norm Deltabred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hDeltabred :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        Deltabred_norm)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hDeltabred_norm_budget :
      Deltabred_norm ≤ eps * vecNorm2 (lsResidualHigham A b x))
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y (lsResidualHigham A b x)
      (lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y)
      heps_nonneg hApos hbpos hBpos hdpos hxpos hyx hrpos hmax
      hMP hBAPt hstack hx hy hN hNpert rfl rfl hAredPlus_pos
      hAred_norm_nonneg hkappa hkappaB hdelta hsmall hAredPlus
      hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
      hDeltabred_norm_budget hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    relative residual-gap form of the MP/transpose-range nullspace-Wedin
    route.  The reduced right-hand-side budget is instantiated by the single
    source-relative residual inequality, so callers no longer supply a
    separate `Deltabred_norm` and budget certificate. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {delta AredPlus_norm DeltaAred_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hDeltaAred :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) DeltaAred_norm)
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hDeltaAred_norm_budget : DeltaAred_norm ≤ eps * Ared_norm)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hDeltabred :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) :=
    (div_le_iff₀ hrpos).mp hres_relative
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residuals
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
      hAredPlus_pos hAred_norm_nonneg hkappa hkappaB hdelta hsmall
      hAredPlus hDelta hDeltaAred hDeltabred hDeltaAred_norm_budget
      le_rfl hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    relative residual-gap form of the MP/transpose-range nullspace-Wedin
    route with the reduced operator budget instantiated by the same Wedin
    smallness radius `delta = eps * ||Ared||`.  This removes the separate
    `DeltaAred_norm` caller obligation while keeping the concrete nullspace
    bases, reduced pseudoinverses, `kappa_B`, and bracket inequality explicit. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_delta
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {delta AredPlus_norm kappa eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : kappa = AredPlus_norm * Ared_norm)
    (hkappaB : kappa = theorem20_8KappaB A APplus)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : kappa * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * kappa ≤
        kappa *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hDelta_budget : delta ≤ eps * Ared_norm := by
    simp [hdelta]
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
      hAredPlus_pos hAred_norm_nonneg hkappa hkappaB hdelta hsmall
      hAredPlus hDelta hDelta hres_relative hDelta_budget hleftA
      hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    relative residual-gap and reduced-operator-budget form with Wedin's
    reduced-condition parameter specialized to the source-facing
    `kappa_B(A)` quantity used in (20.25).  The scalar bracket and reduced
    residual-gap estimate remain explicit obligations. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_delta_kappaB
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {delta AredPlus_norm eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hdelta : delta = eps * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) delta)
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) :=
  LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_delta
    hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
    AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
    hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
    hAredPlus_pos hAred_norm_nonneg hkappa rfl hdelta hsmall
    hAredPlus hDelta hres_relative hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-facing `kappa_B(A)` nullspace-Wedin handoff with the reduced
    operator perturbation radius written directly as `eps * ||Ared||`.  This
    removes the auxiliary `delta` equality while keeping the residual-gap,
    reduced norm identity, smallness, and scalar bracket obligations explicit. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hAred_norm_nonneg : 0 ≤ Ared_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) :=
  LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_delta_kappaB
    hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
    AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
    hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
    hAredPlus_pos hAred_norm_nonneg hkappa rfl hsmall hAredPlus
    hDelta hres_relative hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-facing `kappa_B(A)` direct-radius wrapper deriving the reduced
    operator norm's nonnegativity from `kappa_B(A) >= 0`, a positive
    pseudoinverse norm bound, and the reduced norm identity.  The reduced
    pseudoinverse, source-relative residual-gap, smallness, and bracket
    obligations remain explicit. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB_norm_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hprod_nonneg : 0 ≤ AredPlus_norm * Ared_norm := by
    simpa [hkappa] using theorem20_8KappaB_nonneg A APplus
  have hAred_norm_nonneg : 0 ≤ Ared_norm :=
    (mul_nonneg_iff_of_pos_left hAredPlus_pos).mp hprod_nonneg
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
      hAredPlus_pos hAred_norm_nonneg hkappa hsmall hAredPlus
      hDelta hres_relative hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-facing `kappa_B(A)` direct-radius wrapper with the reduced residual
    gap supplied in norm form rather than divided-relative form.  Since the
    source residual norm is positive, `||rHigh-r|| <= eps*||r||` implies the
    relative residual-gap hypothesis consumed by the Wedin handoff. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_norm_kappaB_norm_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps := by
    exact (div_le_iff₀ hrpos).2 (by simpa using hres_norm)
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB_norm_nonneg
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
      hAredPlus_pos hkappa hsmall hAredPlus hDelta hres_relative
      hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-facing `kappa_B(A)` direct-radius wrapper deriving `eps >= 0` from
    the displayed maximum-relative perturbation budget and positive source
    denominators.  The residual gap is supplied in norm form, while the
    reduced pseudoinverse, reduced operator budget, smallness, and bracket
    obligations remain explicit. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_norm_kappaB_eps_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have heps_nonneg : 0 ≤ eps :=
    (theorem20_8MaxRelativePerturbation_nonneg A DeltaA b Deltab B DeltaB d
      Deltad hApos).trans hmax
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_norm_kappaB_norm_nonneg
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y heps_nonneg hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hMP hBAPt hstack hx hy hN hNpert
      hAredPlus_pos hkappa hsmall hAredPlus hDelta hres_norm
      hleftA hleftB hSymA hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-facing `kappa_B(A)` direct-radius wrapper taking the residual gap
    in divided-relative form while deriving both `eps >= 0` and the norm-form
    residual-gap budget used by the latest source-residual surface. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB_eps_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) :=
    (div_le_iff₀ hrpos).mp hres_relative
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_norm_kappaB_eps_nonneg
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y hApos hbpos hBpos hdpos hxpos hyx hrpos
      hmax hMP hBAPt hstack hx hy hN hNpert hAredPlus_pos hkappa
      hsmall hAredPlus hDelta hres_norm hleftA hleftB hSymA hSymB
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    generic Moore--Penrose/transpose-range handoff where the residual gap is
    supplied by the `B_A^+` split residual decomposition.

    This removes the caller-facing direct residual-norm premise from the
    full-row-rank MP route.  The remaining residual obligation is the explicit
    scalar comparison between the proved BAplus residual-gap RHS and
    `eps * ||r||_2`; the reduced Wedin budgets, smallness guard, and source
    bracket comparison remain visible. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_BAplus_residual_gap_kappaB_eps_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus : rectOpNorm2Le AredPlus AredPlus_norm)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin n => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hgap_le :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
            vecNorm2 (fun j : Fin n => y j - x j) +
          ((theorem20_8KappaB A APplus *
                (complexMatrixOp2
                    (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                  (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
              complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B hB.rightInverse APplus))) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            (eps * frobNormRect A) * vecNorm2 y +
            eps * vecNorm2 b) := by
    simpa using
      theorem20_8_source_residual_gap_norm_le_of_solution_difference_maxRelativePerturbation_BAplus_split
        A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y
        (lsResidualHigham A b x)
        (lsResidualHigham (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i) y)
        hApos hbpos hBpos hdpos hmax hx.1 hy.1 rfl rfl
  have hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) :=
    hgap_le.trans hgapScale
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_norm_kappaB_eps_nonneg
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y hApos hbpos hBpos hdpos hxpos hyx hrpos
      hmax hMP hBAPt hstack hx hy hN hNpert hAredPlus_pos hkappa
      hsmall hAredPlus hDelta hres_norm hleftA hleftB hSymA hSymB
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 route audit:
    the source rank assumptions in (20.24) do not imply the determinant-facing
    Gram condition `det((AP)(AP)^T) != 0` for the concrete full-row-rank
    pseudoinverse construction of `(AP)^+`.

    In this `m = n = 3`, `p = 1` example, `A = I` and `B` selects the first
    coordinate.  Then `B` is full row rank and `[A; B]` has full column rank, but
    `AP = A(I - B^+B)` has rank two, so its `3 x 3` row Gram determinant is
    zero.  Thus the rank-tolerant Moore--Penrose route is genuinely needed for
    the full Theorem 20.8 surface. -/
theorem theorem20_8_gram_AP_rectGram_det_zero_counterexample :
    ∃ (A : Fin 3 → Fin 3 → ℝ) (B : Fin 1 → Fin 3 → ℝ)
      (Bplus : Fin 3 → Fin 1 → ℝ),
      rectMatMul B Bplus = idMatrix 1 ∧
        LSEFullRowRank B ∧
          LSEStackedFullColumnRank A B ∧
            Matrix.det
              (rectGram (theorem20_8AP A B Bplus) :
                Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  let A : Fin 3 → Fin 3 → ℝ := idMatrix 3
  let B : Fin 1 → Fin 3 → ℝ := fun _ j =>
    if j = (0 : Fin 3) then 1 else 0
  let Bplus : Fin 3 → Fin 1 → ℝ := fun j _ =>
    if j = (0 : Fin 3) then 1 else 0
  refine ⟨A, B, Bplus, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [B, Bplus, rectMatMul, idMatrix]
  · intro y
    refine ⟨fun j : Fin 3 => if j = (0 : Fin 3) then y 0 else 0, ?_⟩
    ext i
    fin_cases i
    norm_num [B, lseConstraintLinearMap, rectMatMulVec]
  · intro x y hxy
    have hAxy : rectMatMulVec A x = rectMatMulVec A y := by
      ext i
      have hi := congrFun hxy (Fin.castAdd 1 i)
      rw [congrFun (lseStackedMatrix_mulVec A B x) (Fin.castAdd 1 i)] at hi
      rw [congrFun (lseStackedMatrix_mulVec A B y) (Fin.castAdd 1 i)] at hi
      simpa [Fin.append_left] using hi
    simpa [A, rectMatMulVec_idMatrix] using hAxy
  · simp [A, B, Bplus, theorem20_8AP, theorem20_8Projection, rectMatMul,
      rectGram, idMatrix, Matrix.det_fin_three, eq_comm]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    concrete reduced-pseudoinverse-norm version of the generic MP/BAplus
    residual-gap handoff.

    The reduced left-inverse field implies that the concrete operator norm of
    `AredPlus` is positive, and the repository operator-norm API supplies the
    corresponding `rectOpNorm2Le` certificate. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_BAplus_residual_gap_concreteAredPlusNorm_kappaB_eps_nonneg
    {m n p k : ℕ} (hm : 0 < m)
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (N Npert : Fin n → Fin (k + 1) → ℝ)
    (AredPlus BredPlus : Fin (k + 1) → Fin m → ℝ)
    (x y : Fin n → ℝ)
    {eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hN : rectMatMul B N =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hNpert : rectMatMul (fun i j => B i j + DeltaB i j) Npert =
      (fun _i : Fin p => fun _j : Fin (k + 1) => 0))
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2 (realRectToCMatrix AredPlus) * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) Npert i j -
            rectMatMul A N i j) (eps * Ared_norm))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin n => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hleftA : rectMatMul AredPlus (rectMatMul A N) = idMatrix (k + 1))
    (hleftB :
      rectMatMul BredPlus
          (rectMatMul (fun i j => A i j + DeltaA i j) Npert) =
        idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul (rectMatMul A N) AredPlus))
    (hSymB : IsSymmetricFiniteMatrix
      (rectMatMul (rectMatMul (fun i j => A i j + DeltaA i j) Npert)
        BredPlus))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAredPlus_pos :
      0 < complexMatrixOp2 (realRectToCMatrix AredPlus) :=
    complexMatrixOp2_realRectToCMatrix_pos_of_rect_left_inverse
      (rectMatMul A N) AredPlus hleftA
  have hAredPlus :
      rectOpNorm2Le AredPlus
        (complexMatrixOp2 (realRectToCMatrix AredPlus)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le AredPlus le_rfl
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_BAplus_residual_gap_kappaB_eps_nonneg
      (AredPlus_norm := complexMatrixOp2 (realRectToCMatrix AredPlus))
      (Ared_norm := Ared_norm)
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad N Npert
      AredPlus BredPlus x y hApos hbpos hBpos hdpos hxpos hyx hrpos
      hmax hMP hBAPt hstack hx hy hN hNpert hAredPlus_pos hkappa
      hsmall hAredPlus hDelta hgapScale hleftA hleftB hSymA hSymB
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    GQR-specialized nullspace-Wedin handoff.  Choosing the nullspace bases as
    the concrete trailing `Q₂` columns of supplied source and perturbed GQR
    factorizations discharges the raw nullspace-basis and reduced
    Gram-pseudoinverse fields in the source-facing `kappa_B(A)` wrapper.

    The residual-relative estimate, reduced GQR trailing-block perturbation
    budget, `kappa_B` identity, smallness condition, and scalar bracket
    inequality remain explicit source obligations. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_relative_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        AredPlus_norm)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j) (eps * Ared_norm))
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hm : 0 < r + (k + 1) := by omega
  have hredA := h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  have hredB := hpert.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstackPert
  have hleftA :
      rectMatMul (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMul A h.Q2Basis) =
        idMatrix (k + 1) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredA.1
  have hleftB :
      rectMatMul
          (lsAplusOfGramNonsingInv
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))
          (rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis) =
        idMatrix (k + 1) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredB.1
  have hSymA :
      IsSymmetricFiniteMatrix
        (rectMatMul (rectMatMul A h.Q2Basis)
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredA.2
  have hSymB :
      IsSymmetricFiniteMatrix
        (rectMatMul
          (rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis)
          (lsAplusOfGramNonsingInv
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredB.2
  have hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis i j -
            rectMatMul A h.Q2Basis i j) (eps * Ared_norm) :=
    h.rectOpNorm2Le_reduced_delta_of_gqrAQ2Block hpert hDeltaGQR
  exact
    LSEFullRowRank.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_nullspace_reduced_wedinResidualRHS_kappaB_bracket_MP_transpose_range_lseStackedFullColumnRank_source_residual_relative_kappaB_eps_nonneg
      hm A DeltaA b Deltab hB DeltaB APplus d Deltad h.Q2Basis
      hpert.Q2Basis (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
      (lsAplusOfGramNonsingInv
        (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))
      x y hApos hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack
      hx hy h.Q2Basis_nullspace hpert.Q2Basis_nullspace hAredPlus_pos
      hkappa hsmall hAredPlus hDelta hres_relative hleftA hleftB hSymA
      hSymB hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    GQR-specialized nullspace-Wedin handoff with the residual gap supplied in
    norm form.  The positive source residual norm converts
    `||rHigh-r||₂ <= eps*||r||₂` to the relative residual-gap hypothesis used
    by the GQR `Q₂` reduced-Gram wrapper. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        AredPlus_norm)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j) (eps * Ared_norm))
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps :=
    (div_le_iff₀ hrpos).2 hres_norm
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_relative_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hAredPlus hDeltaGQR hres_relative
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    GQR-specialized nullspace-Wedin handoff with the residual-gap estimate
    supplied by the previously proved `B_A^+` split residual decomposition.

    The remaining scalar hypothesis compares that explicit BAplus residual-gap
    RHS, including the reduced `AP` action on `y-x`, with the source residual
    radius `eps*||r||₂`. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {AredPlus_norm eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos : 0 < AredPlus_norm)
    (hkappa : theorem20_8KappaB A APplus = AredPlus_norm * Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        AredPlus_norm)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j) (eps * Ared_norm))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  let rHigh : Fin (r + (k + 1)) → ℝ :=
    lsResidualHigham (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) y
  have hgap_le :
      vecNorm2
          (fun i : Fin (r + (k + 1)) =>
            rHigh i - lsResidualHigham A b x i) ≤
        complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
            vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
          ((theorem20_8KappaB A APplus *
                (complexMatrixOp2
                    (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                  (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
              complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B hB.rightInverse APplus))) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            (eps * frobNormRect A) * vecNorm2 y +
            eps * vecNorm2 b) := by
    simpa [rHigh] using
      theorem20_8_source_residual_gap_norm_le_of_solution_difference_maxRelativePerturbation_BAplus_split
        A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y
        (lsResidualHigham A b x) rHigh hApos hbpos hBpos hdpos hmax
        hx.1 hy.1 rfl rfl
  have hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) := by
    simpa [rHigh] using hgap_le.trans hgapScale
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hAredPlus hDeltaGQR hres_norm
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    concrete reduced-pseudoinverse-norm version of the GQR/BAplus residual-gap
    handoff.  The reduced pseudoinverse norm bound is discharged by the
    operator norm of the concrete Gram pseudoinverse. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredPlusNorm_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps Ared_norm : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          Ared_norm)
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j) (eps * Ared_norm))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        (complexMatrixOp2
          (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)))) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) le_rfl
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_kappaB_eps_nonneg
      (AredPlus_norm := complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
      (Ared_norm := Ared_norm) A DeltaA b Deltab hB DeltaB APplus d Deltad
      hpert x y hApos hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt
      hstack hstackPert hx hy hAredPlus_pos hkappa hsmall hAredPlus hDeltaGQR
      hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    concrete reduced-norm version of the GQR/BAplus residual-gap handoff.  The
    reduced matrix norm in the Wedin radius is instantiated as the operator
    norm of the concrete trailing GQR block `A Q₂`. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q))))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredPlusNorm_kappaB_eps_nonneg
      (Ared_norm := complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hDeltaGQR hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    Frobenius-budget version of the concrete GQR/BAplus handoff.  A
    Frobenius norm bound for the reduced trailing-block perturbation supplies
    the operator-norm Wedin radius required by the preceding wrapper. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q))) :=
    rectOpNorm2Le_of_frobNormRect_le _ hDeltaGQRFrob
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hDeltaGQR hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    Frobenius-budget concrete GQR/BAplus handoff with the reduced
    Gram-pseudoinverse norm positivity derived from stacked full column rank. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_autoAredPlusPos_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hsmall : theorem20_8KappaB A APplus * eps < 1)
    (hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) :=
    h.A_Q2_reduced_gram_pseudoinverse_op2_pos hstack
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hDeltaGQRFrob hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-shaped smallness version of the Frobenius-budget concrete
    GQR/BAplus handoff.  The source guard `eps < 1 / kappa_B(A)` is converted
    to the multiplied reduced-Wedin guard using the concrete GQR `kappa_B(A)`
    identity and stacked full column rank. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hepsSmall : eps < 1 / theorem20_8KappaB A APplus)
    (hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hkappa_pos :
      0 < theorem20_8KappaB A APplus :=
    h.theorem20_8KappaB_pos_of_gqrQ2_reducedGram_kappa APplus hstack hkappa
  have hsmall : theorem20_8KappaB A APplus * eps < 1 :=
    theorem20_8KappaB_mul_eps_lt_one_of_eps_lt_inv A APplus hkappa_pos hepsSmall
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_autoAredPlusPos_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hkappa hsmall hDeltaGQRFrob hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` full-source-perturbation version of the concrete GQR/BAplus
    handoff.

    When the supplied perturbed GQR factorization uses the same right factor
    `Q` as the source factorization, the full `DeltaA` Frobenius bound is
    transported to the reduced trailing-block budget internally.  The theorem
    keeps the genuinely remaining obligations explicit: the concrete
    `kappa_B(A)` identity, source smallness, BAplus residual-radius comparison,
    and scalar bracket inequality. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_sameQ_deltaA_frob_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hepsSmall : eps < 1 / theorem20_8KappaB A APplus)
    (hQsame : hpert.Q = h.Q)
    (hDeltaAFrob :
      frobNormRect DeltaA ≤
        eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)))
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)) :=
    h.gqrAQ2Block_delta_frobNorm_le_of_same_Q hpert hQsame hDeltaAFrob
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredNorms_of_reduced_frob_delta_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hkappa hepsSmall hDeltaGQRFrob hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius version of the GQR/BAplus handoff.

    The displayed max-relative perturbation hypothesis already gives
    `||DeltaA||_F <= eps*||A||_F`.  If the supplied perturbed GQR record uses
    the same right factor `Q`, this source perturbation budget supplies the
    reduced Wedin radius with `Ared_norm = ||A||_F`.  Thus callers no longer
    provide a separate reduced trailing-block perturbation bound on this
    same-basis route. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_sourceA_frob_sameQ_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          frobNormRect A)
    (hepsSmall : eps < 1 / theorem20_8KappaB A APplus)
    (hQsame : hpert.Q = h.Q)
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) :=
    h.A_Q2_reduced_gram_pseudoinverse_op2_pos hstack
  have hkappa_pos :
      0 < theorem20_8KappaB A APplus := by
    rw [hkappa]
    exact mul_pos hAredPlus_pos hApos
  have hsmall : theorem20_8KappaB A APplus * eps < 1 :=
    theorem20_8KappaB_mul_eps_lt_one_of_eps_lt_inv A APplus hkappa_pos
      hepsSmall
  have hbudget :
      theorem20_8RelativePerturbationBudget A DeltaA b Deltab B DeltaB d Deltad
        eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A DeltaA b Deltab B DeltaB d Deltad hApos hbpos hBpos hdpos hmax
  have hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * frobNormRect A :=
    h.gqrAQ2Block_delta_frobNorm_le_of_same_Q hpert hQsame hbudget.1
  have hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le _ hDeltaGQRFrob
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_concreteAredPlusNorm_kappaB_eps_nonneg
      (Ared_norm := frobNormRect A)
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hDeltaGQR hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius GQR/BAplus handoff with the `kappa_B(A)`
    identification reduced to an operator-norm identity for the chosen
    `(AP)^+`.

    The previous source-radius wrapper asked for the product identity
    `kappa_B(A)=||(A Q₂)^+||₂*||A||_F`.  Since `kappa_B(A)` is defined as
    `||A||_F*||(AP)^+||₂`, this version only asks callers to identify the
    operator norm of their chosen rank-tolerant `(AP)^+` with the concrete
    reduced Gram pseudoinverse norm. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_sourceA_frob_sameQ_APplusNorm_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAPplusNorm :
      complexMatrixOp2 (realRectToCMatrix APplus) =
        complexMatrixOp2
          (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
    (hepsSmall : eps < 1 / theorem20_8KappaB A APplus)
    (hQsame : hpert.Q = h.Q)
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A APplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse APplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          frobNormRect A := by
    unfold theorem20_8KappaB
    rw [hAPplusNorm]
    ring
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_sourceA_frob_sameQ_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hkappa hepsSmall hQsame hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius handoff specialized to the concrete lifted
    reduced-Gram `(AP)^+ = Q₂(AQ₂)^+` candidate.

    The generic same-basis source-radius wrapper asks callers to identify the
    operator norm of an arbitrary rank-tolerant `(AP)^+` with the reduced Gram
    pseudoinverse.  For the lifted reduced-Gram table this equality is proved
    by `liftedReducedGramAPplus_op2_eq`, so this source-facing surface removes
    that premise while preserving the genuine remaining residual-gap,
    smallness, and scalar bracket obligations. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_sourceA_frob_sameQ_liftedReducedGram_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) h.liftedReducedGramAPplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hgapScale :
      complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B hB.rightInverse)) *
          vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) +
        ((theorem20_8KappaB A h.liftedReducedGramAPplus *
              (complexMatrixOp2
                  (realRectToCMatrix (rectMatMul A hB.rightInverse)) *
                (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
            complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse
                      h.liftedReducedGramAPplus))) *
              (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
          (eps * frobNormRect A) * vecNorm2 y +
          eps * vecNorm2 b) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A h.liftedReducedGramAPplus ≤
        theorem20_8KappaB A h.liftedReducedGramAPplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse
                      h.liftedReducedGramAPplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          h.liftedReducedGramAPplus
          (theorem20_8BAplus A B hB.rightInverse h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hB.rightInverse
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B hB.rightInverse
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) :=
  h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_BAplus_residual_gap_sourceA_frob_sameQ_APplusNorm_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    A DeltaA b Deltab hB DeltaB h.liftedReducedGramAPplus d Deltad
    hpert x y hApos hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt
    hstack hstackPert hx hy h.liftedReducedGramAPplus_op2_eq hepsSmall
    hQsame hgapScale hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius GQR handoff with a direct residual-gap norm
    hypothesis and an `(AP)^+` norm-identification hypothesis.

    This is the residual-norm counterpart of the BAplus-residual-gap wrapper:
    callers may supply `||r_high-r||₂ <= eps*||r||₂` directly, while the
    source max-relative perturbation bound and same-`Q` hypothesis still
    produce the reduced `A Q₂` perturbation budget internally. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_sourceA_frob_sameQ_APplusNorm_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAPplusNorm :
      complexMatrixOp2 (realRectToCMatrix APplus) =
        complexMatrixOp2
          (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
    (hepsSmall : eps < 1 / theorem20_8KappaB A APplus)
    (hQsame : hpert.Q = h.Q)
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A APplus ≤
        theorem20_8KappaB A APplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (theorem20_8BAplus A B hB.rightInverse APplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          APplus (theorem20_8BAplus A B hB.rightInverse APplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            APplus (theorem20_8BAplus A B hB.rightInverse APplus) *
          (complexMatrixOp2
              (realRectToCMatrix (theorem20_8BAplus A B hB.rightInverse APplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  have hAredPlus_pos :
      0 < complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) :=
    h.A_Q2_reduced_gram_pseudoinverse_op2_pos hstack
  have hkappa :
      theorem20_8KappaB A APplus =
        complexMatrixOp2
            (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
          frobNormRect A := by
    unfold theorem20_8KappaB
    rw [hAPplusNorm]
    ring
  have hkappa_pos :
      0 < theorem20_8KappaB A APplus := by
    rw [hkappa]
    exact mul_pos hAredPlus_pos hApos
  have hsmall : theorem20_8KappaB A APplus * eps < 1 :=
    theorem20_8KappaB_mul_eps_lt_one_of_eps_lt_inv A APplus hkappa_pos
      hepsSmall
  have hbudget :
      theorem20_8RelativePerturbationBudget A DeltaA b Deltab B DeltaB d Deltad
        eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A DeltaA b Deltab B DeltaB d Deltad hApos hbpos hBpos hdpos hmax
  have hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * frobNormRect A :=
    h.gqrAQ2Block_delta_frobNorm_le_of_same_Q hpert hQsame hbudget.1
  have hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le _ hDeltaGQRFrob
  have hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        (complexMatrixOp2
          (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)))) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) le_rfl
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_kappaB_eps_nonneg
      (AredPlus_norm := complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
      (Ared_norm := frobNormRect A)
      A DeltaA b Deltab hB DeltaB APplus d Deltad hpert x y hApos
      hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert
      hx hy hAredPlus_pos hkappa hsmall hAredPlus hDeltaGQR hres_norm
      hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius GQR handoff with a direct residual-gap norm
    hypothesis, specialized to the concrete lifted reduced-Gram
    `(AP)^+ = Q₂(AQ₂)^+` candidate.

    This removes the caller-facing operator-norm identification required by the
    generic APplus-norm residual-gap wrapper; the equality is supplied by
    `liftedReducedGramAPplus_op2_eq`. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_sourceA_frob_sameQ_liftedReducedGram_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) h.liftedReducedGramAPplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hbracket :
      1 + 2 * theorem20_8KappaB A h.liftedReducedGramAPplus ≤
        theorem20_8KappaB A h.liftedReducedGramAPplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse
                      h.liftedReducedGramAPplus))) +
            1)) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          h.liftedReducedGramAPplus
          (theorem20_8BAplus A B hB.rightInverse h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hB.rightInverse
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B hB.rightInverse
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) :=
  h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_sourceA_frob_sameQ_APplusNorm_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
    A DeltaA b Deltab hB DeltaB h.liftedReducedGramAPplus d Deltad
    hpert x y hApos hbpos hBpos hdpos hxpos hyx hrpos hmax hMP hBAPt
    hstack hstackPert hx hy h.liftedReducedGramAPplus_op2_eq hepsSmall
    hQsame hres_norm hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    residual-factor variant of the same-`Q` source-radius GQR handoff with a
    direct residual-gap norm hypothesis and the concrete lifted reduced-Gram
    `(AP)^+ = Q₂(AQ₂)^+` candidate.

    The scalar premise is the source-facing residual-amplifier lower bound
    `1 + 1/kappa_B(A) <= (||B||_F/||A||_F)||A B_A^+||₂`; positivity of
    `kappa_B(A)` is derived from the lifted table. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_sourceA_frob_sameQ_liftedReducedGram_residualFactor_of_eps_lt_inv_kappaB_eps_nonneg
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B hB.rightInverse) h.liftedReducedGramAPplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B hB.rightInverse
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
          h.liftedReducedGramAPplus
          (theorem20_8BAplus A B hB.rightInverse h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hB.rightInverse
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B hB.rightInverse
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hstack hApos
  have hbracket :
      1 + 2 * theorem20_8KappaB A h.liftedReducedGramAPplus ≤
        theorem20_8KappaB A h.liftedReducedGramAPplus *
          ((frobNormRect B / frobNormRect A) *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A
                    (theorem20_8BAplus A B hB.rightInverse
                      h.liftedReducedGramAPplus))) +
            1) :=
    theorem20_8_kappaB_bracket_of_residual_amplifier_factor_ge_one_add_inv
      A B h.liftedReducedGramAPplus
      (theorem20_8BAplus A B hB.rightInverse h.liftedReducedGramAPplus)
      hkappa_pos hresidualFactor
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_gqrQ2_reducedGram_source_residual_norm_sourceA_frob_sameQ_liftedReducedGram_autoAredPlusPos_of_eps_lt_inv_kappaB_eps_nonneg
      A DeltaA b Deltab hB DeltaB d Deltad hpert x y hApos hbpos hBpos
      hdpos hxpos hyx hrpos hmax hMP hBAPt hstack hstackPert hx hy
      hepsSmall hQsame hres_norm hbracket
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    lifted reduced-Gram Gram-projector handoff whose Wedin residual-relative
    estimate is supplied by the concrete source and perturbed GQR `Q₂` reduced
    problems.

    This wrapper composes the reduced-nullspace Wedin theorem with the
    minimizer-facing lifted residual-factor surface.  The remaining analytical
    obligations are the reduced trailing-block perturbation budget, the source
    residual-relative budget, the source smallness condition
    `eps < 1/kappa_B(A)`, and the residual-amplifier lower-bound factor. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_of_eps_lt_inv_kappaB
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * frobNormRect A))
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hm : 0 < r + (k + 1) := by omega
  have heps_nonneg : 0 ≤ eps :=
    (theorem20_8MaxRelativePerturbation_nonneg A DeltaA b Deltab B DeltaB d
      Deltad hApos).trans hmax
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hstack hApos
  have hsmall :
      theorem20_8KappaB A h.liftedReducedGramAPplus * eps < 1 :=
    theorem20_8KappaB_mul_eps_lt_one_of_eps_lt_inv
      A h.liftedReducedGramAPplus hkappa_pos hepsSmall
  have hredA := h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  have hredB := hpert.A_Q2_reduced_gram_left_inverse_and_projection_symmetric
    hstackPert
  have hleftA :
      rectMatMul (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMul A h.Q2Basis) =
        idMatrix (k + 1) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredA.1
  have hleftB :
      rectMatMul
          (lsAplusOfGramNonsingInv
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))
          (rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis) =
        idMatrix (k + 1) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredB.1
  have hSymA :
      IsSymmetricFiniteMatrix
        (rectMatMul (rectMatMul A h.Q2Basis)
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredA.2
  have hSymB :
      IsSymmetricFiniteMatrix
        (rectMatMul
          (rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis)
          (lsAplusOfGramNonsingInv
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))) := by
    simpa [GeneralizedQRFactorization.A_mul_Q2Basis] using hredB.2
  have hAredPlus :
      rectOpNorm2Le (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        (complexMatrixOp2
          (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)))) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) le_rfl
  have hDelta :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (fun i j => A i j + DeltaA i j) hpert.Q2Basis i j -
            rectMatMul A h.Q2Basis i j)
        (eps * frobNormRect A) :=
    h.rectOpNorm2Le_reduced_delta_of_gqrAQ2Block hpert hDeltaGQR
  have hDeltabred :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) :=
    (div_le_iff₀ hrpos).1 hres_relative
  have hrelative :
      vecNorm2
          (fun i =>
            lsResidualHigham A b x i -
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        wedinTheorem20_1ResidualRelativeRHS
          (theorem20_8KappaB A h.liftedReducedGramAPplus) eps :=
    theorem20_8_nullspace_reduced_wedinResidualRHS_le_of_lse_minimizers
      (delta := eps * frobNormRect A)
      (AredPlus_norm := complexMatrixOp2
        (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))))
      (DeltaAred_norm := eps * frobNormRect A)
      (Deltabred_norm := eps * vecNorm2 (lsResidualHigham A b x))
      (kappa := theorem20_8KappaB A h.liftedReducedGramAPplus)
      (eps := eps) (Ared_norm := frobNormRect A)
      hm A DeltaA b Deltab B DeltaB d Deltad h.Q2Basis hpert.Q2Basis
      (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
      (lsAplusOfGramNonsingInv
        (gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q))
      x y (lsResidualHigham A b x)
      (lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y)
      hx hy h.Q2Basis_nullspace hpert.Q2Basis_nullspace rfl rfl hrpos
      (h.A_Q2_reduced_gram_pseudoinverse_op2_pos hstack) hApos.le
      heps_nonneg h.theorem20_8KappaB_liftedReducedGramAPplus_eq rfl hsmall
      hAredPlus hDelta hDelta hDeltabred le_rfl le_rfl hleftA hleftB
      hSymA hSymB
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_wedinResidualRHS_residualFactor_of_minimizers
      A DeltaA b Deltab hB DeltaB d Deltad x y hApos hbpos hBpos hdpos
      hxpos hyx hrpos hmax hstack hx hy hrelative hresidualFactor
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius specialization of the lifted Gram-projector
    reduced-Wedin residual-factor wrapper, with the residual gap supplied in
    divided relative form.

    This is the same reduced trailing-block handoff as the norm-form wrapper
    below, but it lets callers reuse a source-relative residual estimate
    directly. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_relative_of_eps_lt_inv_kappaB
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hbudget :
      theorem20_8RelativePerturbationBudget A DeltaA b Deltab B DeltaB d Deltad
        eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A DeltaA b Deltab B DeltaB d Deltad hApos hbpos hBpos hdpos hmax
  have hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * frobNormRect A :=
    h.gqrAQ2Block_delta_frobNorm_le_of_same_Q hpert hQsame hbudget.1
  have hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le _ hDeltaGQRFrob
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_of_eps_lt_inv_kappaB
      A DeltaA b Deltab hB DeltaB d Deltad hpert x y hApos hbpos hBpos
      hdpos hxpos hyx hrpos hmax hstack hstackPert hx hy hepsSmall
      hDeltaGQR hres_relative hresidualFactor
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius specialization of the lifted Gram-projector
    reduced-Wedin residual-factor wrapper, with the divided residual gap stated
    in the source-minus-perturbed order.

    The immediately preceding wrapper uses the perturbed-minus-source residual
    convention.  This version is mathematically identical but matches the
    source-facing residual order used by the lower-level Wedin handoff. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_relative_source_minus_of_eps_lt_inv_kappaB
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham A b x i -
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps)
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hres_relative' :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps := by
    rwa [vecNorm2_sub_comm
      (fun i =>
        lsResidualHigham (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i) y i)
      (lsResidualHigham A b x)]
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_relative_of_eps_lt_inv_kappaB
      A DeltaA b Deltab hB DeltaB d Deltad hpert x y hApos hbpos hBpos
      hdpos hxpos hyx hrpos hmax hstack hstackPert hx hy hepsSmall hQsame
      hres_relative' hresidualFactor
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius specialization of the lifted Gram-projector
    reduced-Wedin residual-factor wrapper.

    The displayed max-relative perturbation budget supplies the reduced
    trailing-block perturbation bound when the perturbed GQR factorization
    reuses the source `Q`, and the source residual gap is accepted in norm
    form. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_of_eps_lt_inv_kappaB
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hbudget :
      theorem20_8RelativePerturbationBudget A DeltaA b Deltab B DeltaB d Deltad
        eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A DeltaA b Deltab B DeltaB d Deltad hApos hbpos hBpos hdpos hmax
  have hDeltaGQRFrob :
      frobNormRect
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        ≤ eps * frobNormRect A :=
    h.gqrAQ2Block_delta_frobNorm_le_of_same_Q hpert hQsame hbudget.1
  have hDeltaGQR :
      rectOpNorm2Le
        (fun i j =>
          gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
            gqrAQ2Block A h.Q i j)
        (eps * frobNormRect A) :=
    rectOpNorm2Le_of_frobNormRect_le _ hDeltaGQRFrob
  have hres_relative :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) /
          vecNorm2 (lsResidualHigham A b x) ≤
        eps :=
    (div_le_iff₀ hrpos).2 hres_norm
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_of_eps_lt_inv_kappaB
      A DeltaA b Deltab hB DeltaB d Deltad hpert x y hApos hbpos hBpos
      hdpos hxpos hyx hrpos hmax hstack hstackPert hx hy hepsSmall
      hDeltaGQR hres_relative hresidualFactor
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    same-`Q` source-radius specialization of the lifted Gram-projector
    reduced-Wedin residual-factor wrapper with the residual estimate supplied
    in the source-minus-perturbed norm order.

    This is the norm-form counterpart of the relative source-minus wrapper and
    keeps the same real mathematical obligations explicit. -/
theorem
    GeneralizedQRFactorization.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_source_minus_of_eps_lt_inv_kappaB
    {r p k : ℕ}
    (A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ)
    (b Deltab : Fin (r + (k + 1)) → ℝ)
    {B : Fin p → Fin (p + (k + 1)) → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin (p + (k + 1)) → ℝ)
    (d Deltad : Fin p → ℝ)
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hpert : GeneralizedQRFactorization r p (k + 1)
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (x y : Fin (p + (k + 1)) → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hrpos : 0 < vecNorm2 (lsResidualHigham A b x))
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hstack : LSEStackedFullColumnRank A B)
    (hstackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j))
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hepsSmall : eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus)
    (hQsame : hpert.Q = h.Q)
    (hres_norm :
      vecNorm2
          (fun i =>
            lsResidualHigham A b x i -
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i) ≤
        eps * vecNorm2 (lsResidualHigham A b x))
    (hresidualFactor :
      1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)))) :
    vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
      eps *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) +
        eps ^ 2 *
          theorem20_8FirstOrderRHS A b B d x (lsResidualHigham A b x)
            h.liftedReducedGramAPplus
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
              h.liftedReducedGramAPplus) *
          (complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                  h.liftedReducedGramAPplus)) *
              frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A) := by
  have hres_norm' :
      vecNorm2
          (fun i =>
            lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i -
              lsResidualHigham A b x i) ≤
        eps * vecNorm2 (lsResidualHigham A b x) := by
    rwa [vecNorm2_sub_comm
      (fun i =>
        lsResidualHigham (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i) y i)
      (lsResidualHigham A b x)]
  exact
    h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_of_eps_lt_inv_kappaB
      A DeltaA b Deltab hB DeltaB d Deltad hpert x y hApos hbpos hBpos
      hdpos hxpos hyx hrpos hmax hstack hstackPert hx hy hepsSmall hQsame
      hres_norm' hresidualFactor
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    perturbed-rank witness package for the reduced `AP` problem.

    If the perturbed LSE data satisfy the two rank conditions in (20.24), then
    there are a perturbed feasible base point, a perturbed LSE minimizer, and
    the corresponding reduced least-squares minimizer.  The reduced Higham
    residual is orthogonal to the columns of the perturbed reduced `AP`
    matrix, which is the exact optimality side needed by the Wedin residual
    route. -/
theorem theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_conditions20_24
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (d Deltad : Fin p → ℝ)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hStackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)) :
    ∃ (x0 y : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
      LSEFeasible (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x0 ∧
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
      IsLeastSquaresMinimizer
          (theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
          (fun j => y j - x0 j) ∧
      s =
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
              rectMatMulVec
                (theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                (fun j => y j - x0 j) i) ∧
      (∀ j : Fin (p + q),
        ∑ i : Fin (r + q),
          theorem20_8AP (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
            s i = 0) := by
  rcases hBpert.exists_feasible (fun i => d i + Deltad i) with
    ⟨x0, hx0⟩
  rcases exists_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i)
      (d := fun i => d i + Deltad i) hBpert hStackPert with
    ⟨y, hy⟩
  let s : Fin (r + q) → ℝ :=
    fun i =>
      b i + Deltab i -
        rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
        rectMatMulVec
          (theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
          (fun j => y j - x0 j) i
  have hred :
      IsLeastSquaresMinimizer
          (theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
          (fun j => y j - x0 j) :=
    LSEFullRowRank.theorem20_8AP_perturbed_unconstrained_minimizer_of_lse_minimizer
      A DeltaA b Deltab B DeltaB hBpert d Deltad x0 y hx0 hy
  have horth :
      ∀ j : Fin (p + q),
        ∑ i : Fin (r + q),
          theorem20_8AP (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
            s i = 0 :=
    LSEFullRowRank.theorem20_8AP_perturbed_reduced_higham_residual_orthogonal_of_lse_minimizer
      A DeltaA b Deltab B DeltaB hBpert d Deltad x0 y s hx0 hy rfl
  exact ⟨x0, y, s, hx0, hy, hred, rfl, horth⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    uniqueness-enhanced perturbed-rank witness package for the reduced `AP`
    problem.

    This is the base same-witness layer for the reduced `AP` route under the
    perturbed rank assumptions: the feasible base point, reduced
    least-squares minimizer proof, and reduced residual orthogonality witness
    are attached to the unique perturbed LSE minimizer. -/
theorem
    theorem20_8_exists_unique_perturbed_lse_minimizer_and_reduced_minimizer_orthogonal_of_conditions20_24
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (d Deltad : Fin p → ℝ)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hStackPert : LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)) :
    ∃! y : Fin (p + q) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ (x0 : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + q),
            ∑ i : Fin (r + q),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) := by
  rcases exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i)
      (d := fun i => d i + Deltad i) hBpert hStackPert with
    ⟨_yuniq, _hyuniq, huniq⟩
  rcases theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_conditions20_24
      A DeltaA b Deltab B DeltaB d Deltad hBpert hStackPert with
    ⟨x0, y, s, hfeas, hy, hred, hs, horth⟩
  refine ⟨y, ⟨hy, x0, s, hfeas, hred, hs, horth⟩, ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    maximum-relative-perturbation version of the reduced `AP` witness package.

    Source rank conditions and strict margin smallness first preserve (20.24)
    for the perturbed problem; the resulting perturbed rank facts then supply
    the reduced minimizer and residual orthogonality witnesses. -/
theorem
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lt_margins
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {eps : ℝ}
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hBsmall :
      eps * frobNormRect B < hBsrc.transposeVecNorm2LowerMargin)
    (hStackSmall :
      eps * frobNormRect A + eps * frobNormRect B <
        hStack.vecNorm2LowerMargin) :
    ∃ (x0 y : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
      LSEFeasible (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x0 ∧
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
      IsLeastSquaresMinimizer
          (theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)
            (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
              hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse)
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
          (fun j => y j - x0 j) ∧
      s =
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
              rectMatMulVec
                (theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j)
                  (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
                    hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse)
                (fun j => y j - x0 j) i) ∧
      (∀ j : Fin (p + q),
        ∑ i : Fin (r + q),
          theorem20_8AP (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j)
              (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
                hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse i j *
            s i = 0) := by
  let hcond :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall
  exact
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_conditions20_24
      A DeltaA b Deltab B DeltaB d Deltad hcond.1 hcond.2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    maximum-relative-perturbation version of the reduced `AP` witness package,
    with uniqueness of the perturbed LSE minimizer.

    The margin hypotheses preserve the perturbed rank conditions and provide a
    reduced least-squares witness.  This wrapper ties that reduced witness to
    the unique perturbed LSE minimizer rather than returning an arbitrary
    minimizer. -/
theorem
    theorem20_8_exists_unique_perturbed_lse_minimizer_and_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lt_margins
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {eps : ℝ}
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hBsmall :
      eps * frobNormRect B < hBsrc.transposeVecNorm2LowerMargin)
    (hStackSmall :
      eps * frobNormRect A + eps * frobNormRect B <
        hStack.vecNorm2LowerMargin) :
    ∃! y : Fin (p + q) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ (x0 : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j)
                (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
                  hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j)
                      (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
                        hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + q),
            ∑ i : Fin (r + q),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j)
                  (theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
                    hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall).1.rightInverse i j *
                s i = 0) := by
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨_yuniq, _hyuniq, huniq⟩
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨x0, y, s, hfeas, hy, hred, hs, horth⟩
  refine ⟨y, ⟨hy, x0, s, hfeas, hred, hs, horth⟩, ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    one-threshold version of the reduced `AP` witness package.

    The combined rank/KKT smallness threshold discharges the two strict
    rank-preservation margins used to obtain perturbed (20.24).  The conclusion
    returns those perturbed rank facts together with the feasible base point,
    perturbed LSE minimizer, reduced `AP` least-squares minimizer proof, and
    reduced residual orthogonality witness. -/
theorem
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {eps : ℝ}
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
    ∃ _hStackPert : LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j),
    ∃ (x0 y : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
      LSEFeasible (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x0 ∧
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
      IsLeastSquaresMinimizer
          (theorem20_8AP (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
          (fun j => y j - x0 j) ∧
      s =
          (fun i =>
            b i + Deltab i -
              rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
              rectMatMulVec
                (theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                (fun j => y j - x0 j) i) ∧
      (∀ j : Fin (p + q),
        ∑ i : Fin (r + q),
          theorem20_8AP (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
            s i = 0) := by
  rcases theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  let hcond :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall
  rcases theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_of_conditions20_24
      A DeltaA b Deltab B DeltaB d Deltad hcond.1 hcond.2 with
    ⟨x0, y, s, hfeas, hy, hred, hs, horth⟩
  exact ⟨hcond.1, hcond.2, x0, y, s, hfeas, hy, hred, hs, horth⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    one-threshold unique perturbed-minimizer version of the reduced `AP`
    witness package.

    This is the base uniqueness layer for the reduced `AP` route: the same
    perturbed minimizer that carries the feasible base point, reduced
    least-squares proof, and reduced residual orthogonality is identified as
    the unique minimizer of the perturbed LSE problem. -/
theorem
    theorem20_8_exists_unique_perturbed_lse_minimizer_and_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {eps : ℝ}
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + q) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + q),
            ∑ i : Fin (r + q),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) := by
  rcases theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨_yuniq, _hyuniq, huniq⟩
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  refine
    ⟨y,
      ⟨hy, hBpert, hStackPert, x0, s, hfeas, hred, hs, horth⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    source-rank package tying the perturbed reduced-`AP` witness to the
    source-residual KKT fallback bound.

    The rank/KKT threshold preserves the perturbed (20.24) ranks, giving a
    perturbed feasible base point, the perturbed LSE minimizer, the reduced
    `AP` least-squares minimizer, and reduced residual orthogonality.  The same
    perturbed minimizer is then used in the source-residual KKT direct/data
    correction bound with the source lifted reduced-Gram `(AP)^+` candidate. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_sourceResidual_kkt_bound_and_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + q),
            ∑ i : Fin (r + q),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2
                (fun j : Fin (p + q) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + q) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + q) (p + q)
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + q) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  have hbound :
      (vecNorm2
            (fun j : Fin (p + q) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + q) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, hMP, hnull, hBpert, hStackPert, x0, y, s,
      hfeas, hy, hred, hs, horth, hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer reduced-`AP`/source-residual KKT same-witness package.

    This strengthens the reduced-`AP`/KKT package above by using the rank
    preservation margins to identify the perturbed LSE minimizer as unique.
    The lifted reduced-Gram `(AP)^+`, reduced `AP` optimality witness,
    reduced residual orthogonality, and source-residual KKT fallback are all
    tied to that same unique perturbed minimizer. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_sourceResidual_kkt_bound_and_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + q) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
          RectMoorePenrosePseudoinverse (r + q) (p + q)
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
            rectMatMul B APplus =
              (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
            ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
            ∃ _hStackPert : LSEStackedFullColumnRank
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ (x0 : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
              LSEFeasible (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i) x0 ∧
              IsLeastSquaresMinimizer
                  (theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                  (fun j => y j - x0 j) ∧
              s =
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                      rectMatMulVec
                        (theorem20_8AP (fun i j => A i j + DeltaA i j)
                          (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                        (fun j => y j - x0 j) i) ∧
              (∀ j : Fin (p + q),
                ∑ i : Fin (r + q),
                  theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                    s i = 0) ∧
              (vecNorm2
                    (fun j : Fin (p + q) =>
                      rectMatMulVec
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                          (fun i : Fin p =>
                            Deltad i - rectMatMulVec DeltaB y i) j +
                        rectMatMulVec APplus
                          (fun i : Fin (r + q) =>
                            rectMatMulVec DeltaA y i - Deltab i) j) +
                  eps * theorem20_8ResidualAmplifier A B APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                    (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                  vecNorm2 x ≤
                eps * theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                  eps *
                    theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                      ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                        A B).2 hStack) b x eps *
                    (complexMatrixOp2
                        (realRectToCMatrix
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                        frobNormRect B +
                      complexMatrixOp2 (realRectToCMatrix APplus) *
                        frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨_yuniq, _hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_sourceResidual_kkt_bound_and_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, hMP, hnull, hBpert, hStackPert, x0, y, s, hfeas, hy, hred,
      hs, horth, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, hMP, hnull, hBpert, hStackPert, x0, s, hfeas, hred,
        hs, horth, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    source-rank package tying the perturbed reduced-`AP` witness to both the
    additive-scaled residual-gap solution-difference handoff and the
    source-residual KKT fallback bound.

    This theorem deliberately keeps the residual-gap component estimates
    explicit.  Its purpose is to ensure that the reduced minimizer, reduced
    residual orthogonality, rank-tolerant source `(AP)^+`, nonnegative
    `kappa_B(A)` certificate, solution-difference implication, and KKT fallback
    bound all refer to the same perturbed minimizer selected from the one
    combined rank/KKT smallness threshold. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps gapAP gapCorr : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
        RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
        0 ≤ theorem20_8KappaB A APplus ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + q),
            ∑ i : Fin (r + q),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2 y ≤ vecNorm2 x →
            (complexMatrixOp2 (realRectToCMatrix APplus) *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) *
                  vecNorm2 (fun j : Fin (p + q) => y j - x j)) ≤
              gapAP) →
            (complexMatrixOp2 (realRectToCMatrix APplus) *
                ((theorem20_8KappaB A APplus *
                      (complexMatrixOp2
                          (realRectToCMatrix
                            (rectMatMul A (undetAplusOfGramNonsingInv B))) *
                        (eps * vecNorm2 d + (eps * frobNormRect B) *
                          vecNorm2 y)) +
                    complexMatrixOp2
                        (realRectToCMatrix
                          (rectMatMul A
                            (theorem20_8BAplus A B
                              (undetAplusOfGramNonsingInv B) APplus))) *
                      (eps * vecNorm2 d + (eps * frobNormRect B) *
                        vecNorm2 y)) +
                  (eps * frobNormRect A) * vecNorm2 y +
                  eps * vecNorm2 b) ≤
              gapCorr) →
            (gapAP + gapCorr ≤
              eps * theorem20_8ResidualAmplifier A B APplus
                  (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                    APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) →
            let BAplus :=
              theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
            let firstOrder :=
              theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus BAplus
            let dataCoeff :=
              complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
            vecNorm2 (fun j : Fin (p + q) => y j - x j) / vecNorm2 x ≤
              eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
          (vecNorm2
                (fun j : Fin (p + q) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + q) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + q) (p + q)
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + q) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  have hkappa_nonneg :
      0 ≤ theorem20_8KappaB A h.liftedReducedGramAPplus :=
    theorem20_8KappaB_nonneg A h.liftedReducedGramAPplus
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  have hsolution :
      (vecNorm2 y ≤ vecNorm2 x →
        (complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) *
              vecNorm2 (fun j : Fin (p + q) => y j - x j)) ≤
          gapAP) →
        (complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
            ((theorem20_8KappaB A h.liftedReducedGramAPplus *
                  (complexMatrixOp2
                      (realRectToCMatrix
                        (rectMatMul A (undetAplusOfGramNonsingInv B))) *
                    (eps * vecNorm2 d + (eps * frobNormRect B) *
                      vecNorm2 y)) +
                complexMatrixOp2
                    (realRectToCMatrix
                      (rectMatMul A
                        (theorem20_8BAplus A B
                          (undetAplusOfGramNonsingInv B)
                          h.liftedReducedGramAPplus))) *
                  (eps * vecNorm2 d + (eps * frobNormRect B) *
                    vecNorm2 y)) +
              (eps * frobNormRect A) * vecNorm2 y +
              eps * vecNorm2 b) ≤
          gapCorr) →
        (gapAP + gapCorr ≤
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
              (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) →
        let BAplus :=
          theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
            h.liftedReducedGramAPplus
        let firstOrder :=
          theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus BAplus
        let dataCoeff :=
          complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A
        vecNorm2 (fun j : Fin (p + q) => y j - x j) / vecNorm2 x ≤
          eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) := by
    intro hy_norm hgapScaleAP hgapScaleCorr hgapScale
    dsimp
    exact
      h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_BAplus_residual_gap_additive_scaled_of_minimizers
        A DeltaA b Deltab hBsrc DeltaB d Deltad x y hApos hbpos hBpos
        hdpos hxnorm hy_norm hmax hStack hx hy hgapScaleAP hgapScaleCorr
        hgapScale
  have hbound :
      (vecNorm2
            (fun j : Fin (p + q) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + q) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, hMP, hnull, hkappa_nonneg, hBpert, hStackPert,
      x0, y, s, hfeas, hy, hred, hs, horth, hsolution, hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer same-witness package for the additive-scaled residual-gap
    route and source-residual KKT fallback.

    This strengthens the generic same-witness package above by using the rank
    preservation margins to identify the perturbed LSE minimizer as unique.
    The lifted reduced-Gram `(AP)^+`, reduced `AP` optimality witness,
    additive-scaled solution implication, and source-residual KKT fallback are
    all tied to that same unique perturbed minimizer. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Deltab : Fin (r + q) → ℝ}
    {B DeltaB : Fin p → Fin (p + q) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps gapAP gapCorr : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + q) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
          RectMoorePenrosePseudoinverse (r + q) (p + q)
            (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
          rectMatMul B APplus =
            (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
          0 ≤ theorem20_8KappaB A APplus ∧
          ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
          ∃ _hStackPert : LSEStackedFullColumnRank
              (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j),
          ∃ (x0 : Fin (p + q) → ℝ) (s : Fin (r + q) → ℝ),
            LSEFeasible (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x0 ∧
            IsLeastSquaresMinimizer
                (theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                (fun i =>
                  b i + Deltab i -
                    rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                (fun j => y j - x0 j) ∧
            s =
                (fun i =>
                  b i + Deltab i -
                    rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                    rectMatMulVec
                      (theorem20_8AP (fun i j => A i j + DeltaA i j)
                        (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                      (fun j => y j - x0 j) i) ∧
            (∀ j : Fin (p + q),
              ∑ i : Fin (r + q),
                theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                  s i = 0) ∧
            (vecNorm2 y ≤ vecNorm2 x →
              (complexMatrixOp2 (realRectToCMatrix APplus) *
                  (complexMatrixOp2
                      (realRectToCMatrix
                        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) *
                    vecNorm2 (fun j : Fin (p + q) => y j - x j)) ≤
                gapAP) →
              (complexMatrixOp2 (realRectToCMatrix APplus) *
                  ((theorem20_8KappaB A APplus *
                        (complexMatrixOp2
                            (realRectToCMatrix
                              (rectMatMul A (undetAplusOfGramNonsingInv B))) *
                          (eps * vecNorm2 d + (eps * frobNormRect B) *
                            vecNorm2 y)) +
                      complexMatrixOp2
                          (realRectToCMatrix
                            (rectMatMul A
                              (theorem20_8BAplus A B
                                (undetAplusOfGramNonsingInv B) APplus))) *
                        (eps * vecNorm2 d + (eps * frobNormRect B) *
                          vecNorm2 y)) +
                    (eps * frobNormRect A) * vecNorm2 y +
                    eps * vecNorm2 b) ≤
                gapCorr) →
              (gapAP + gapCorr ≤
                eps * theorem20_8ResidualAmplifier A B APplus
                    (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
                      APplus) *
                  (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) →
              let BAplus :=
                theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
              let firstOrder :=
                theorem20_8FirstOrderRHS A b B d x
                  (lsResidualHigham A b x) APplus BAplus
              let dataCoeff :=
                complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
              vecNorm2 (fun j : Fin (p + q) => y j - x j) / vecNorm2 x ≤
                eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
            (vecNorm2
                  (fun j : Fin (p + q) =>
                    rectMatMulVec
                        (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                        (fun i : Fin p =>
                          Deltad i - rectMatMulVec DeltaB y i) j +
                      rectMatMulVec APplus
                        (fun i : Fin (r + q) =>
                          rectMatMulVec DeltaA y i - Deltab i) j) +
                eps * theorem20_8ResidualAmplifier A B APplus
                  (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                  (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                vecNorm2 x ≤
              eps * theorem20_8FirstOrderRHS A b B d x
                  (lsResidualHigham A b x) APplus
                  (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                eps *
                  theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                      A B).2 hStack) b x eps *
                  (complexMatrixOp2
                      (realRectToCMatrix
                        (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                      frobNormRect B +
                    complexMatrixOp2 (realRectToCMatrix APplus) *
                      frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨_yuniq, _hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      (eps := eps) (gapAP := gapAP) (gapCorr := gapCorr)
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, hMP, hnull, hkappa_nonneg, hBpert, hStackPert, x0, y, s,
      hfeas, hy, hred, hs, horth, hsolution, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, hMP, hnull, hkappa_nonneg, hBpert, hStackPert, x0, s,
        hfeas, hred, hs, horth, hsolution, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    coefficient residual-gap solution-difference handoff and the
    source-residual KKT fallback bound, using the same perturbed minimizer.

    This is the nonempty-reduced-block counterpart of the same-witness package
    above.  It uses the existing coefficient residual-gap route, so the
    genuinely separate scalar obligations remain explicit: `||y||₂ <= ||x||₂`,
    the reduced-`AP` small-gain product, the source residual-radius coefficient
    bound, and the residual-factor lower bound. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_solution_difference_coeff_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
        RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
        0 < theorem20_8KappaB A APplus ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + (k + 1)) → ℝ)
          (s : Fin (r + (k + 1)) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + (k + 1)),
            ∑ i : Fin (r + (k + 1)),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2 y ≤ vecNorm2 x →
            (complexMatrixOp2 (realRectToCMatrix APplus) *
                complexMatrixOp2
                  (realRectToCMatrix
                    (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) <
              1) →
            (theorem20_8BAplusSmallGainResidualRadiusCoeff A b B
                (undetAplusOfGramNonsingInv B) APplus d x ≤
              vecNorm2 (lsResidualHigham A b x)) →
            (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
              (frobNormRect B / frobNormRect A) *
                complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B
                        (undetAplusOfGramNonsingInv B) APplus)))) →
            let BAplus :=
              theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
            let firstOrder :=
              theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus BAplus
            let dataCoeff :=
              complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
            vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
              eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
          (vecNorm2
                (fun j : Fin (p + (k + 1)) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + (k + 1)) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hStack hApos
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  have hsolution :
      (vecNorm2 y ≤ vecNorm2 x →
        (complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
            complexMatrixOp2
              (realRectToCMatrix
                (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) <
          1) →
        (theorem20_8BAplusSmallGainResidualRadiusCoeff A b B
            (undetAplusOfGramNonsingInv B) h.liftedReducedGramAPplus d x ≤
          vecNorm2 (lsResidualHigham A b x)) →
        (1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
          (frobNormRect B / frobNormRect A) *
            complexMatrixOp2
              (realRectToCMatrix
                (rectMatMul A
                  (theorem20_8BAplus A B
                    (undetAplusOfGramNonsingInv B)
                    h.liftedReducedGramAPplus)))) →
        let BAplus :=
          theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
            h.liftedReducedGramAPplus
        let firstOrder :=
          theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus BAplus
        let dataCoeff :=
          complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A
        vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) / vecNorm2 x ≤
          eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) := by
    intro hy_norm hgain hcoeff hresidualFactor
    simpa using
      h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_BAplus_residual_gap_small_gain_coeff_of_minimizers
        A DeltaA b Deltab hBsrc DeltaB d Deltad x y hApos hbpos hBpos
        hdpos hxnorm hy_norm hmax hStack hx hy hgain hcoeff
        hresidualFactor
  have hbound :
      (vecNorm2
            (fun j : Fin (p + (k + 1)) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + (k + 1)) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, hMP, hnull, hkappa_pos, hBpert, hStackPert,
      x0, y, s, hfeas, hy, hred, hs, horth, hsolution, hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer reduced-block same-witness package for the coefficient
    residual-gap route and source-residual KKT fallback.

    This strengthens the coefficient same-witness package by using the rank
    preservation margins to identify the perturbed LSE minimizer as unique.
    The lifted reduced-Gram `(AP)^+`, reduced `AP` optimality witness,
    coefficient-based solution implication, and source-residual KKT fallback
    are all tied to that same unique perturbed minimizer. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_solution_difference_coeff_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + (k + 1)) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
          RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
            (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
          rectMatMul B APplus =
            (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
          0 < theorem20_8KappaB A APplus ∧
          ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
          ∃ _hStackPert : LSEStackedFullColumnRank
              (fun i j => A i j + DeltaA i j)
              (fun i j => B i j + DeltaB i j),
          ∃ (x0 : Fin (p + (k + 1)) → ℝ)
            (s : Fin (r + (k + 1)) → ℝ),
            LSEFeasible (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x0 ∧
            IsLeastSquaresMinimizer
                (theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                (fun i =>
                  b i + Deltab i -
                    rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                (fun j => y j - x0 j) ∧
            s =
                (fun i =>
                  b i + Deltab i -
                    rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                    rectMatMulVec
                      (theorem20_8AP (fun i j => A i j + DeltaA i j)
                        (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                      (fun j => y j - x0 j) i) ∧
            (∀ j : Fin (p + (k + 1)),
              ∑ i : Fin (r + (k + 1)),
                theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                  s i = 0) ∧
            (vecNorm2 y ≤ vecNorm2 x →
              (complexMatrixOp2 (realRectToCMatrix APplus) *
                  complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) <
                1) →
              (theorem20_8BAplusSmallGainResidualRadiusCoeff A b B
                  (undetAplusOfGramNonsingInv B) APplus d x ≤
                vecNorm2 (lsResidualHigham A b x)) →
              (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
                (frobNormRect B / frobNormRect A) *
                  complexMatrixOp2
                    (realRectToCMatrix
                      (rectMatMul A
                        (theorem20_8BAplus A B
                          (undetAplusOfGramNonsingInv B) APplus)))) →
              let BAplus :=
                theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
              let firstOrder :=
                theorem20_8FirstOrderRHS A b B d x
                  (lsResidualHigham A b x) APplus BAplus
              let dataCoeff :=
                complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
              vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                  vecNorm2 x ≤
                eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
            (vecNorm2
                  (fun j : Fin (p + (k + 1)) =>
                    rectMatMulVec
                        (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                        (fun i : Fin p =>
                          Deltad i - rectMatMulVec DeltaB y i) j +
                      rectMatMulVec APplus
                        (fun i : Fin (r + (k + 1)) =>
                          rectMatMulVec DeltaA y i - Deltab i) j) +
                eps * theorem20_8ResidualAmplifier A B APplus
                  (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                  (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                vecNorm2 x ≤
              eps * theorem20_8FirstOrderRHS A b B d x
                  (lsResidualHigham A b x) APplus
                  (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                eps *
                  theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                      A B).2 hStack) b x eps *
                  (complexMatrixOp2
                      (realRectToCMatrix
                        (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                      frobNormRect B +
                    complexMatrixOp2 (realRectToCMatrix APplus) *
                      frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨yuniq, hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_solution_difference_coeff_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, hMP, hnull, hkappa_pos, hBpert, hStackPert, x0, y, s, hfeas,
      hy, hred, hs, horth, hsolution, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, hMP, hnull, hkappa_pos, hBpert, hStackPert, x0, s,
        hfeas, hred, hs, horth, hsolution, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nonempty reduced-block same-witness package for the direct
    source-residual-relative solution-difference route and the source-residual
    KKT fallback.

    This is the direct residual-relative counterpart of the coefficient and
    reduced-Wedin packages below.  It uses the lifted reduced-Gram `(AP)^+`
    selected from the source ranks and keeps the same perturbed minimizer and
    reduced residual orthogonality witness for both the first-order-plus-`eps^2`
    solution implication and the source-residual KKT fallback.  The residual
    relative estimate and residual-factor lower bound remain explicit. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_source_residual_relative_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
        0 < theorem20_8KappaB A APplus ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + (k + 1)) → ℝ)
          (s : Fin (r + (k + 1)) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + (k + 1)),
            ∑ i : Fin (r + (k + 1)),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2 y ≤ vecNorm2 x →
            0 < vecNorm2 (lsResidualHigham A b x) →
            (vecNorm2
                (fun i =>
                  lsResidualHigham A b x i -
                    lsResidualHigham (fun i j => A i j + DeltaA i j)
                      (fun i => b i + Deltab i) y i) /
                vecNorm2 (lsResidualHigham A b x) ≤
              eps) →
            (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
              (frobNormRect B / frobNormRect A) *
                complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B
                        (undetAplusOfGramNonsingInv B) APplus)))) →
            let BAplus :=
              theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
            let firstOrder :=
              theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus BAplus
            let dataCoeff :=
              complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
            vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                vecNorm2 x ≤
              eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
          (vecNorm2
                (fun j : Fin (p + (k + 1)) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + (k + 1)) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hStack hApos
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  have hsolution :
      (vecNorm2 y ≤ vecNorm2 x →
        0 < vecNorm2 (lsResidualHigham A b x) →
        (vecNorm2
            (fun i =>
              lsResidualHigham A b x i -
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i) /
            vecNorm2 (lsResidualHigham A b x) ≤
          eps) →
        (1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
          (frobNormRect B / frobNormRect A) *
            complexMatrixOp2
              (realRectToCMatrix
                (rectMatMul A
                  (theorem20_8BAplus A B
                    (undetAplusOfGramNonsingInv B)
                    h.liftedReducedGramAPplus)))) →
        let BAplus :=
          theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
            h.liftedReducedGramAPplus
        let firstOrder :=
          theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus BAplus
        let dataCoeff :=
          complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A
        vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
            vecNorm2 x ≤
          eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) := by
    intro hy_norm hrpos hrelative hresidualFactor
    simpa using
      h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_source_residual_relative_residualFactor_source_minus_of_minimizers
        A DeltaA b Deltab hBsrc DeltaB d Deltad x y hApos hbpos hBpos
        hdpos hxnorm hy_norm hrpos hmax hStack hx hy hrelative
        hresidualFactor
  have hbound :
      (vecNorm2
            (fun j : Fin (p + (k + 1)) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + (k + 1)) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, hMP, hnull, hkappa_pos, hBpert, hStackPert,
      x0, y, s, hfeas, hy, hred, hs, horth, hsolution, hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer reduced-block same-witness package for the direct
    source-residual-relative route and source-residual KKT fallback.

    This strengthens the nonempty same-witness package by using the rank
    preservation margins to identify the perturbed minimizer as unique.  The
    returned `y` is therefore both the unique perturbed LSE minimizer and the
    minimizer used by the reduced `AP` optimality witness, the direct
    source-minus residual-relative implication, and the source-residual KKT
    fallback. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_source_residual_relative_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + (k + 1)) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
          RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
            rectMatMul B APplus =
              (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
            0 < theorem20_8KappaB A APplus ∧
            ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
            ∃ _hStackPert : LSEStackedFullColumnRank
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ (x0 : Fin (p + (k + 1)) → ℝ)
              (s : Fin (r + (k + 1)) → ℝ),
              LSEFeasible (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i) x0 ∧
              IsLeastSquaresMinimizer
                  (theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                  (fun j => y j - x0 j) ∧
              s =
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                      rectMatMulVec
                        (theorem20_8AP (fun i j => A i j + DeltaA i j)
                          (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                        (fun j => y j - x0 j) i) ∧
              (∀ j : Fin (p + (k + 1)),
                ∑ i : Fin (r + (k + 1)),
                  theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                    s i = 0) ∧
              (vecNorm2 y ≤ vecNorm2 x →
                0 < vecNorm2 (lsResidualHigham A b x) →
                (vecNorm2
                    (fun i =>
                      lsResidualHigham A b x i -
                        lsResidualHigham (fun i j => A i j + DeltaA i j)
                          (fun i => b i + Deltab i) y i) /
                    vecNorm2 (lsResidualHigham A b x) ≤
                  eps) →
                (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
                  (frobNormRect B / frobNormRect A) *
                    complexMatrixOp2
                      (realRectToCMatrix
                        (rectMatMul A
                          (theorem20_8BAplus A B
                            (undetAplusOfGramNonsingInv B) APplus)))) →
                let BAplus :=
                  theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
                let firstOrder :=
                  theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus BAplus
                let dataCoeff :=
                  complexMatrixOp2 (realRectToCMatrix BAplus) *
                      frobNormRect B +
                    complexMatrixOp2 (realRectToCMatrix APplus) *
                      frobNormRect A
                vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                    vecNorm2 x ≤
                  eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
              (vecNorm2
                    (fun j : Fin (p + (k + 1)) =>
                      rectMatMulVec
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                          (fun i : Fin p =>
                            Deltad i - rectMatMulVec DeltaB y i) j +
                        rectMatMulVec APplus
                          (fun i : Fin (r + (k + 1)) =>
                            rectMatMulVec DeltaA y i - Deltab i) j) +
                  eps * theorem20_8ResidualAmplifier A B APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                    (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                  vecNorm2 x ≤
                eps * theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                  eps *
                    theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                      ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                        A B).2 hStack) b x eps *
                    (complexMatrixOp2
                        (realRectToCMatrix
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                        frobNormRect B +
                      complexMatrixOp2 (realRectToCMatrix APplus) *
                        frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨yuniq, hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_source_residual_relative_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, hMP, hnull, hkappa_pos, hBpert, hStackPert, x0, y, s, hfeas,
      hy, hred, hs, horth, hsolution, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, hMP, hnull, hkappa_pos, hBpert, hStackPert, x0, s,
        hfeas, hred, hs, horth, hsolution, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    nonempty reduced-block same-witness package for the GQR `Q₂` reduced
    Wedin residual route and the source-residual KKT fallback.

    The package chooses both the source and perturbed GQR factorizations from
    the source and preserved rank conditions, returns the lifted reduced-Gram
    rank-tolerant `(AP)^+`, and keeps the same perturbed minimizer/reduced
    residual orthogonality witness for both the reduced-Wedin solution
    implication and the KKT fallback.  The real remaining analytic obligations
    are still explicit: `||y||₂ <= ||x||₂`, positive source residual, Wedin
    smallness, a same-`Q` reduced perturbation handoff, the source residual
    relative estimate, and the residual-factor lower bound. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
    ∃ h : GeneralizedQRFactorization r p (k + 1) A B,
      APplus = h.liftedReducedGramAPplus ∧
        RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
        0 < theorem20_8KappaB A APplus ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ hpert : GeneralizedQRFactorization r p (k + 1)
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + (k + 1)) → ℝ)
          (s : Fin (r + (k + 1)) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + (k + 1)),
            ∑ i : Fin (r + (k + 1)),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2 y ≤ vecNorm2 x →
            0 < vecNorm2 (lsResidualHigham A b x) →
            eps < 1 / theorem20_8KappaB A APplus →
            hpert.Q = h.Q →
            (vecNorm2
                (fun i =>
                  lsResidualHigham A b x i -
                    lsResidualHigham (fun i j => A i j + DeltaA i j)
                      (fun i => b i + Deltab i) y i) /
                vecNorm2 (lsResidualHigham A b x) ≤
              eps) →
            (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
              (frobNormRect B / frobNormRect A) *
                complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B
                        (undetAplusOfGramNonsingInv B) APplus)))) →
            let BAplus :=
              theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
            let firstOrder :=
              theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus BAplus
            let dataCoeff :=
              complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
            vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                vecNorm2 x ≤
              eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
          (vecNorm2
                (fun j : Fin (p + (k + 1)) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + (k + 1)) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hStack hApos
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j) hBpert hStackPert with
    ⟨hpert⟩
  have hsolution :
      (vecNorm2 y ≤ vecNorm2 x →
        0 < vecNorm2 (lsResidualHigham A b x) →
        eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus →
        hpert.Q = h.Q →
        (vecNorm2
            (fun i =>
              lsResidualHigham A b x i -
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i) /
            vecNorm2 (lsResidualHigham A b x) ≤
          eps) →
        (1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
          (frobNormRect B / frobNormRect A) *
            complexMatrixOp2
              (realRectToCMatrix
                (rectMatMul A
                  (theorem20_8BAplus A B
                    (undetAplusOfGramNonsingInv B)
                    h.liftedReducedGramAPplus)))) →
        let BAplus :=
          theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
            h.liftedReducedGramAPplus
        let firstOrder :=
          theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus BAplus
        let dataCoeff :=
          complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A
        vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
            vecNorm2 x ≤
          eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) := by
    intro hy_norm hrpos hepsSmall hQsame hrelative hresidualFactor
    simpa using
      h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_sourceA_frob_sameQ_relative_source_minus_of_eps_lt_inv_kappaB
        A DeltaA b Deltab hBsrc DeltaB d Deltad hpert x y hApos hbpos
        hBpos hdpos hxnorm hy_norm hrpos hmax hStack hStackPert hx hy
        hepsSmall hQsame hrelative hresidualFactor
  have hbound :
      (vecNorm2
            (fun j : Fin (p + (k + 1)) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + (k + 1)) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, h, rfl, hMP, hnull, hkappa_pos, hBpert,
      hStackPert, hpert, x0, y, s, hfeas, hy, hred, hs, horth, hsolution,
      hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer same-witness package for the concrete GQR `Q₂`
    reduced-Wedin route and source-residual KKT fallback.

    This strengthens the nonempty GQR `Q₂` package by using the rank
    preservation margins to identify the perturbed LSE minimizer as unique.
    The source and perturbed GQR witnesses, lifted reduced-Gram `(AP)^+`,
    reduced `AP` optimality witness, reduced-Wedin solution implication, and
    source-residual KKT fallback are therefore all tied to one unique
    perturbed minimizer. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + (k + 1)) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
        ∃ h : GeneralizedQRFactorization r p (k + 1) A B,
          APplus = h.liftedReducedGramAPplus ∧
            RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
            rectMatMul B APplus =
              (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
            0 < theorem20_8KappaB A APplus ∧
            ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
            ∃ _hStackPert : LSEStackedFullColumnRank
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ hpert : GeneralizedQRFactorization r p (k + 1)
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ (x0 : Fin (p + (k + 1)) → ℝ)
              (s : Fin (r + (k + 1)) → ℝ),
              LSEFeasible (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i) x0 ∧
              IsLeastSquaresMinimizer
                  (theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                  (fun j => y j - x0 j) ∧
              s =
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                      rectMatMulVec
                        (theorem20_8AP (fun i j => A i j + DeltaA i j)
                          (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                        (fun j => y j - x0 j) i) ∧
              (∀ j : Fin (p + (k + 1)),
                ∑ i : Fin (r + (k + 1)),
                  theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                    s i = 0) ∧
              (vecNorm2 y ≤ vecNorm2 x →
                0 < vecNorm2 (lsResidualHigham A b x) →
                eps < 1 / theorem20_8KappaB A APplus →
                hpert.Q = h.Q →
                (vecNorm2
                    (fun i =>
                      lsResidualHigham A b x i -
                        lsResidualHigham (fun i j => A i j + DeltaA i j)
                          (fun i => b i + Deltab i) y i) /
                    vecNorm2 (lsResidualHigham A b x) ≤
                  eps) →
                (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
                  (frobNormRect B / frobNormRect A) *
                    complexMatrixOp2
                      (realRectToCMatrix
                        (rectMatMul A
                          (theorem20_8BAplus A B
                            (undetAplusOfGramNonsingInv B) APplus)))) →
                let BAplus :=
                  theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
                let firstOrder :=
                  theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus BAplus
                let dataCoeff :=
                  complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                    complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
                vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                    vecNorm2 x ≤
                  eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
              (vecNorm2
                    (fun j : Fin (p + (k + 1)) =>
                      rectMatMulVec
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                          (fun i : Fin p =>
                            Deltad i - rectMatMulVec DeltaB y i) j +
                        rectMatMulVec APplus
                          (fun i : Fin (r + (k + 1)) =>
                            rectMatMulVec DeltaA y i - Deltab i) j) +
                  eps * theorem20_8ResidualAmplifier A B APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                    (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                  vecNorm2 x ≤
                eps * theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                  eps *
                    theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                      ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                        A B).2 hStack) b x eps *
                    (complexMatrixOp2
                        (realRectToCMatrix
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                        frobNormRect B +
                      complexMatrixOp2 (realRectToCMatrix APplus) *
                        frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨yuniq, hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, h, hAPeq, hMP, hnull, hkappa_pos, hBpert, hStackPert, hpert,
      x0, y, s, hfeas, hy, hred, hs, horth, hsolution, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, h, hAPeq, hMP, hnull, hkappa_pos, hBpert, hStackPert,
        hpert, x0, s, hfeas, hred, hs, horth, hsolution, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    general GQR `Q₂` reduced-Wedin same-witness package.

    This is the non-same-`Q` counterpart of
    `exists_rank_tolerant_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold`.
    The reduced trailing-block perturbation is supplied directly as a
    `gqrAQ2Block` operator-norm bound, so callers need not identify the source
    and perturbed `Q` factors.  The perturbed minimizer, reduced residual
    orthogonality witness, reduced-Wedin solution implication, and KKT fallback
    still refer to the same chosen perturbed solution. -/
theorem
    IsLSEMinimizer.exists_rank_tolerant_general_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
    ∃ h : GeneralizedQRFactorization r p (k + 1) A B,
      APplus = h.liftedReducedGramAPplus ∧
        RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
        0 < theorem20_8KappaB A APplus ∧
        ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
        ∃ _hStackPert : LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ hpert : GeneralizedQRFactorization r p (k + 1)
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j),
        ∃ (x0 y : Fin (p + (k + 1)) → ℝ)
          (s : Fin (r + (k + 1)) → ℝ),
          LSEFeasible (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x0 ∧
          IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) y ∧
          IsLeastSquaresMinimizer
              (theorem20_8AP (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
              (fun j => y j - x0 j) ∧
          s =
              (fun i =>
                b i + Deltab i -
                  rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                  rectMatMulVec
                    (theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                    (fun j => y j - x0 j) i) ∧
          (∀ j : Fin (p + (k + 1)),
            ∑ i : Fin (r + (k + 1)),
              theorem20_8AP (fun i j => A i j + DeltaA i j)
                  (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                s i = 0) ∧
          (vecNorm2 y ≤ vecNorm2 x →
            0 < vecNorm2 (lsResidualHigham A b x) →
            eps < 1 / theorem20_8KappaB A APplus →
            rectOpNorm2Le
              (fun i j =>
                gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
                  gqrAQ2Block A h.Q i j)
              (eps * frobNormRect A) →
            (vecNorm2
                (fun i =>
                  lsResidualHigham (fun i j => A i j + DeltaA i j)
                      (fun i => b i + Deltab i) y i -
                    lsResidualHigham A b x i) /
                vecNorm2 (lsResidualHigham A b x) ≤
              eps) →
            (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
              (frobNormRect B / frobNormRect A) *
                complexMatrixOp2
                  (realRectToCMatrix
                    (rectMatMul A
                      (theorem20_8BAplus A B
                        (undetAplusOfGramNonsingInv B) APplus)))) →
            let BAplus :=
              theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
            let firstOrder :=
              theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus BAplus
            let dataCoeff :=
              complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
            vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                vecNorm2 x ≤
              eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
          (vecNorm2
                (fun j : Fin (p + (k + 1)) =>
                  rectMatMulVec (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                      (fun i : Fin p =>
                        Deltad i - rectMatMulVec DeltaB y i) j +
                    rectMatMulVec APplus
                      (fun i : Fin (r + (k + 1)) =>
                        rectMatMulVec DeltaA y i - Deltab i) j) +
              eps * theorem20_8ResidualAmplifier A B APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
              vecNorm2 x ≤
            eps * theorem20_8FirstOrderRHS A b B d x
                (lsResidualHigham A b x) APplus
                (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
              eps *
                theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                  ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                    A B).2 hStack) b x eps *
                (complexMatrixOp2
                    (realRectToCMatrix
                      (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                    frobNormRect B +
                  complexMatrixOp2 (realRectToCMatrix APplus) *
                    frobNormRect A) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hBsrc hStack with
    ⟨h⟩
  have hMP :
      RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
        h.liftedReducedGramAPplus :=
    h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
      hBsrc hStack
  have hnull :
      rectMatMul B h.liftedReducedGramAPplus =
        (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) :=
    h.liftedReducedGramAPplus_constraint_annihilates
  have hkappa_pos :
      0 < theorem20_8KappaB A h.liftedReducedGramAPplus :=
    h.theorem20_8KappaB_liftedReducedGramAPplus_pos hStack hApos
  rcases
    theorem20_8_exists_perturbed_reduced_minimizer_orthogonal_with_ranks_of_maxRelativePerturbation_rank_kkt_smallnessThreshold
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hsmall with
    ⟨hBpert, hStackPert, x0, y, s, hfeas, hy, hred, hs, horth⟩
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j) hBpert hStackPert with
    ⟨hpert⟩
  have hsolution :
      (vecNorm2 y ≤ vecNorm2 x →
        0 < vecNorm2 (lsResidualHigham A b x) →
        eps < 1 / theorem20_8KappaB A h.liftedReducedGramAPplus →
        rectOpNorm2Le
          (fun i j =>
            gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
              gqrAQ2Block A h.Q i j)
          (eps * frobNormRect A) →
        (vecNorm2
            (fun i =>
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i -
                lsResidualHigham A b x i) /
            vecNorm2 (lsResidualHigham A b x) ≤
          eps) →
        (1 + (theorem20_8KappaB A h.liftedReducedGramAPplus)⁻¹ ≤
          (frobNormRect B / frobNormRect A) *
            complexMatrixOp2
              (realRectToCMatrix
                (rectMatMul A
                  (theorem20_8BAplus A B
                    (undetAplusOfGramNonsingInv B)
                    h.liftedReducedGramAPplus)))) →
        let BAplus :=
          theorem20_8BAplus A B (undetAplusOfGramNonsingInv B)
            h.liftedReducedGramAPplus
        let firstOrder :=
          theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus BAplus
        let dataCoeff :=
          complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
            complexMatrixOp2 (realRectToCMatrix h.liftedReducedGramAPplus) *
              frobNormRect A
        vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
            vecNorm2 x ≤
          eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) := by
    intro hy_norm hrpos hepsSmall hDeltaGQR hrelative hresidualFactor
    simpa using
      h.theorem20_8_solution_difference_relative_le_firstOrderRHS_plus_eps_sq_coefficient_of_liftedReducedGram_sourceKappaB_gramProjection_gqrQ2_reduced_wedinResidualRHS_residualFactor_of_eps_lt_inv_kappaB
        A DeltaA b Deltab hBsrc DeltaB d Deltad hpert x y hApos hbpos
        hBpos hdpos hxnorm hy_norm hrpos hmax hStack hStackPert hx hy
        hepsSmall hDeltaGQR hrelative hresidualFactor
  have hbound :
      (vecNorm2
            (fun j : Fin (p + (k + 1)) =>
              rectMatMulVec
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)
                  (fun i : Fin p =>
                    Deltad i - rectMatMulVec DeltaB y i) j +
                rectMatMulVec h.liftedReducedGramAPplus
                  (fun i : Fin (r + (k + 1)) =>
                    rectMatMulVec DeltaA y i - Deltab i) j) +
          eps * theorem20_8ResidualAmplifier A B h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) *
            (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
          vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) h.liftedReducedGramAPplus
            (theorem20_8BAplus A B hBsrc.rightInverse
              h.liftedReducedGramAPplus) +
          eps *
            theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
              ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                A B).2 hStack) b x eps *
            (complexMatrixOp2
                (realRectToCMatrix
                  (theorem20_8BAplus A B hBsrc.rightInverse
                    h.liftedReducedGramAPplus)) *
                frobNormRect B +
              complexMatrixOp2
                  (realRectToCMatrix h.liftedReducedGramAPplus) *
                frobNormRect A) :=
    h.theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_KKTSourceResidualRatioCoupledBound_sourceRightInverse_liftedReducedGram_sourceResidual_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hy hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall
  exact
    ⟨h.liftedReducedGramAPplus, h, rfl, hMP, hnull, hkappa_pos, hBpert,
      hStackPert, hpert, x0, y, s, hfeas, hy, hred, hs, horth, hsolution,
      hbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    unique-minimizer same-witness package for the general GQR `Q₂`
    reduced-Wedin route and source-residual KKT fallback.

    This is the unique-minimizer counterpart of the general reduced-Wedin
    package.  It keeps the reduced trailing-block perturbation as an explicit
    `gqrAQ2Block` operator-norm premise, while tying the source and perturbed
    GQR witnesses, lifted reduced-Gram `(AP)^+`, reduced `AP` optimality
    witness, reduced-Wedin solution implication, and source-residual KKT
    fallback to the unique perturbed minimizer. -/
theorem
    IsLSEMinimizer.exists_unique_perturbed_lse_minimizer_and_rank_tolerant_general_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
    {r p k : ℕ}
    {A DeltaA : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {b Deltab : Fin (r + (k + 1)) → ℝ}
    {B DeltaB : Fin p → Fin (p + (k + 1)) → ℝ}
    {d Deltad : Fin p → ℝ} {x : Fin (p + (k + 1)) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A DeltaA b Deltab B DeltaB d Deltad
        ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hBsrc hStack) :
    ∃! y : Fin (p + (k + 1)) → ℝ,
      IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) y ∧
        ∃ APplus : Fin (p + (k + 1)) → Fin (r + (k + 1)) → ℝ,
        ∃ h : GeneralizedQRFactorization r p (k + 1) A B,
          APplus = h.liftedReducedGramAPplus ∧
            RectMoorePenrosePseudoinverse (r + (k + 1)) (p + (k + 1))
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
            rectMatMul B APplus =
              (fun _i : Fin p => fun _j : Fin (r + (k + 1)) => 0) ∧
            0 < theorem20_8KappaB A APplus ∧
            ∃ hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j),
            ∃ _hStackPert : LSEStackedFullColumnRank
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ hpert : GeneralizedQRFactorization r p (k + 1)
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
            ∃ (x0 : Fin (p + (k + 1)) → ℝ)
              (s : Fin (r + (k + 1)) → ℝ),
              LSEFeasible (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i) x0 ∧
              IsLeastSquaresMinimizer
                  (theorem20_8AP (fun i j => A i j + DeltaA i j)
                    (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
                  (fun j => y j - x0 j) ∧
              s =
                  (fun i =>
                    b i + Deltab i -
                      rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i -
                      rectMatMulVec
                        (theorem20_8AP (fun i j => A i j + DeltaA i j)
                          (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
                        (fun j => y j - x0 j) i) ∧
              (∀ j : Fin (p + (k + 1)),
                ∑ i : Fin (r + (k + 1)),
                  theorem20_8AP (fun i j => A i j + DeltaA i j)
                      (fun i j => B i j + DeltaB i j) hBpert.rightInverse i j *
                    s i = 0) ∧
              (vecNorm2 y ≤ vecNorm2 x →
                0 < vecNorm2 (lsResidualHigham A b x) →
                eps < 1 / theorem20_8KappaB A APplus →
                rectOpNorm2Le
                  (fun i j =>
                    gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
                      gqrAQ2Block A h.Q i j)
                  (eps * frobNormRect A) →
                (vecNorm2
                    (fun i =>
                      lsResidualHigham (fun i j => A i j + DeltaA i j)
                          (fun i => b i + Deltab i) y i -
                        lsResidualHigham A b x i) /
                    vecNorm2 (lsResidualHigham A b x) ≤
                  eps) →
                (1 + (theorem20_8KappaB A APplus)⁻¹ ≤
                  (frobNormRect B / frobNormRect A) *
                    complexMatrixOp2
                      (realRectToCMatrix
                        (rectMatMul A
                          (theorem20_8BAplus A B
                            (undetAplusOfGramNonsingInv B) APplus)))) →
                let BAplus :=
                  theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus
                let firstOrder :=
                  theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus BAplus
                let dataCoeff :=
                  complexMatrixOp2 (realRectToCMatrix BAplus) * frobNormRect B +
                    complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A
                vecNorm2 (fun j : Fin (p + (k + 1)) => y j - x j) /
                    vecNorm2 x ≤
                  eps * firstOrder + eps ^ 2 * firstOrder * dataCoeff) ∧
              (vecNorm2
                    (fun j : Fin (p + (k + 1)) =>
                      rectMatMulVec
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)
                          (fun i : Fin p =>
                            Deltad i - rectMatMulVec DeltaB y i) j +
                        rectMatMulVec APplus
                          (fun i : Fin (r + (k + 1)) =>
                            rectMatMulVec DeltaA y i - Deltab i) j) +
                  eps * theorem20_8ResidualAmplifier A B APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) *
                    (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
                  vecNorm2 x ≤
                eps * theorem20_8FirstOrderRHS A b B d x
                    (lsResidualHigham A b x) APplus
                    (theorem20_8BAplus A B hBsrc.rightInverse APplus) +
                  eps *
                    theorem20_8KKTSourceResidualRatioCoupledBound hBsrc
                      ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank
                        A B).2 hStack) b x eps *
                    (complexMatrixOp2
                        (realRectToCMatrix
                          (theorem20_8BAplus A B hBsrc.rightInverse APplus)) *
                        frobNormRect B +
                      complexMatrixOp2 (realRectToCMatrix APplus) *
                        frobNormRect A) := by
  rcases
    theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hBsrc hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, _hKKTsmall⟩
  rcases theorem20_8_exists_unique_perturbed_lse_minimizer_of_maxRelativePerturbation_lt_margins
      (A := A) (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (B := B) (DeltaB := DeltaB) (d := d) (Deltad := Deltad)
      hBsrc hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall with
    ⟨yuniq, hyuniq, huniq⟩
  rcases
    IsLSEMinimizer.exists_rank_tolerant_general_gqrQ2_reduced_wedin_solution_difference_and_sourceResidual_kkt_bound_with_perturbed_reduced_minimizer_orthogonal_of_maxRelativePerturbation_lseStackedFullColumnRank_rank_kkt_smallnessThreshold
      hx hBsrc hStack hxnorm hApos hbpos hBpos hdpos hmax hsmall with
    ⟨APplus, h, hAPeq, hMP, hnull, hkappa_pos, hBpert, hStackPert, hpert,
      x0, y, s, hfeas, hy, hred, hs, horth, hsolution, hbound⟩
  refine
    ⟨y,
      ⟨hy, APplus, h, hAPeq, hMP, hnull, hkappa_pos, hBpert, hStackPert,
        hpert, x0, s, hfeas, hred, hs, horth, hsolution, hbound⟩,
      ?_⟩
  intro z hz
  exact (huniq z hz.1).trans (huniq y hy).symm

end NumStability
