import Mathlib.LinearAlgebra.Matrix.Vec
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Diagonal
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.SchurCoordinates
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.GeneralizedEquations.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation.SeparationBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation.Vectorization
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation10
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation11
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation12
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation13
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation15
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation16
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation18
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation19
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation21
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.LyapunovDefinition
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation23
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation24
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.Equation01
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.Equation02
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.Equation03
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.Equation09
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation22
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation25
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation26
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation27
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.LyapunovSolutions
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation28
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29
import NumStability.Source.Higham.Chapter16.Section05.GeneralizedMatrixEquations.Equation30
import NumStability.Source.Higham.Chapter16.Section05.GeneralizedMatrixEquations.Equation31
import NumStability.Source.Higham.Chapter16.Section05.GeneralizedMatrixEquations.Equation32

/-!
# Algorithms.Sylvester.Higham16

Historical compatibility facade. The genuine-private reverse closure remains here with its original declaration identity.
-/

-- Algorithms/Sylvester/Higham16.lean
--
-- Source-facing Chapter 16 surfaces for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed.  This file complements the older square
-- Frobenius-norm Sylvester infrastructure in `SylvesterSpec`,
-- `SylvesterBackward`, and `SylvesterPerturbation`.





namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Rectangular source equations
-- ============================================================

























































-- ============================================================
-- Vec/Kronecker formulation from Chapter 16.1
-- ============================================================
































































































































































































































-- ============================================================
-- Practical max-entry error bounds from Chapter 16.4
-- ============================================================














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Exact Schur-coordinate algebra from Chapter 16.1
-- ============================================================

private theorem rectMatMul_left_right_sub {m n p q : Nat}
    (A : Fin m -> Fin n -> Real) (B C : Fin n -> Fin p -> Real)
    (D : Fin p -> Fin q -> Real) :
    rectMatMul A (rectMatMul (fun i j => B i j - C i j) D) =
      fun i j => rectMatMul A (rectMatMul B D) i j -
        rectMatMul A (rectMatMul C D) i j := by
  ext i j
  unfold rectMatMul
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      B k k1 * D k1 j))
    (g := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      C k k1 * D k1 j))).symm]
  apply Finset.sum_congr rfl
  intro k _
  rw [(mul_sub (A i k)
    (Finset.sum Finset.univ (fun k1 : Fin p => B k k1 * D k1 j))
    (Finset.sum Finset.univ (fun k1 : Fin p => C k k1 * D k1 j))).symm]
  apply congrArg (fun z => A i k * z)
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k1 : Fin p => B k k1 * D k1 j)
    (g := fun k1 : Fin p => C k k1 * D k1 j)).symm]
  apply Finset.sum_congr rfl
  intro k1 _
  ring

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    exact Sylvester-operator algebra in supplied Schur coordinates.  If
    `A = U R U^T`, `B = V S V^T`, and `U,V` are orthogonal, then
    substituting `X = U Y V^T` transforms `AX - XB` into
    `U (RY - YS) V^T`.  This conditional wrapper does not assert existence
    of Schur decompositions or any triangular/quasi-triangular structure. -/
theorem sylvester_schur_transform_identity (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) =
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) := by
  subst A
  subst B
  have hUtU : rectMatMul (matTranspose U) U = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hVtV : rectMatMul (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.left_inv i j
  have hleft :
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul R (matTranspose U))
              (rectMatMul U (rectMatMul Y (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (matTranspose U) (rectMatMul U (rectMatMul Y (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (rectMatMul (matTranspose U) U) (rectMatMul Y (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul R Z))
                (rectMatMul_assoc (matTranspose U) U (rectMatMul Y (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (idMatrix m) (rectMatMul Y (matTranspose V)))) := by
              rw [hUtU]
      _ = rectMatMul U (rectMatMul R (rectMatMul Y (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc R Y (matTranspose V)).symm
  have hright :
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul Y (matTranspose V))
              (rectMatMul V (rectMatMul S (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (matTranspose V) (rectMatMul V (rectMatMul S (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (rectMatMul (matTranspose V) V) (rectMatMul S (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul Y Z))
                (rectMatMul_assoc (matTranspose V) V (rectMatMul S (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (idMatrix n) (rectMatMul S (matTranspose V)))) := by
              rw [hVtV]
      _ = rectMatMul U (rectMatMul Y (rectMatMul S (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc Y S (matTranspose V)).symm
  have hcombine :
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) =
        fun i j => rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) i j -
          rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) i j := by
    simpa [sylvesterOpRect, matMulRect_eq_rectMatMul] using
      (rectMatMul_left_right_sub U (rectMatMul R Y) (rectMatMul Y S) (matTranspose V))
  unfold sylvesterOpRect
  simp only [matMulRect_eq_rectMatMul]
  rw [hleft, hright]
  exact hcombine.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    source-numbered alias for the supplied Schur-coordinate Sylvester
    operator identity. -/
alias H16_eq16_4_5_sylvester_schur_transform_identity :=
  sylvester_schur_transform_identity



































































/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.5) and (16.9):
    exact residual transport under supplied orthogonal Schur coordinates.
    If `A = U R U^T`, `B = V S V^T`, and `Xhat = U Y V^T`, then the original
    residual is `U` times the Schur-coordinate residual times `V^T`. -/
theorem sylvesterResidualRect_schur_transform_identity (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    sylvesterResidualRect m n A B C
        (rectMatMul U (rectMatMul Y (matTranspose V))) =
      rectMatMul U
        (rectMatMul
          (sylvesterResidualRect m n R S
            (rectMatMul (matTranspose U) (rectMatMul C V)) Y)
          (matTranspose V)) := by
  let Cs : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  have hCexpand : rectMatMul U (rectMatMul Cs (matTranspose V)) = C := by
    simpa [Cs] using rectMatMul_schur_coords_expand U V C hU hV
  have hop :=
    sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
  have hsub :=
    rectMatMul_left_right_sub U Cs (sylvesterOpRect m n R S Y) (matTranspose V)
  ext i j
  unfold sylvesterResidualRect
  rw [hop]
  have hCij := congrFun (congrFun hCexpand i) j
  have hsubij := congrFun (congrFun hsub i) j
  rw [← hCij, ← hsubij]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.5) and (16.9):
    source-numbered alias for exact residual transport under supplied
    orthogonal Schur coordinates. -/
alias H16_eq16_5_9_sylvesterResidualRect_schur_transform_identity :=
  sylvesterResidualRect_schur_transform_identity

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), exact residual norm
    transport for supplied orthogonal Schur coordinates.  This is the
    exact-arithmetic norm bridge used before any rounded Schur-solve residual
    model is introduced. -/
theorem frobNormRect_sylvesterResidualRect_schur_transform (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) =
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) := by
  let Rs : RMatFn m n :=
    sylvesterResidualRect m n R S
      (rectMatMul (matTranspose U) (rectMatMul C V)) Y
  rw [sylvesterResidualRect_schur_transform_identity m n U R A V S B C Y
    hU hV hA hB]
  calc
    frobNormRect (rectMatMul U (rectMatMul Rs (matTranspose V))) =
        frobNormRect (rectMatMul Rs (matTranspose V)) := by
          simpa [Rs, matMulRectLeft] using
            frobNormRect_orthogonal_left U
              (rectMatMul Rs (matTranspose V)) hU
    _ = frobNormRect Rs := by
          simpa [Rs, matMulRectRight] using
            frobNormRect_orthogonal_right Rs (matTranspose V) hV.transpose

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9): source-numbered alias
    for exact Frobenius residual norm transport under supplied orthogonal
    Schur coordinates. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_schur_transform :=
  frobNormRect_sylvesterResidualRect_schur_transform

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), conditional exact
    residual-bound transport.  Any Schur-coordinate Frobenius residual bound
    transfers unchanged to the reconstructed original-coordinate iterate. -/
theorem frobNormRect_sylvesterResidualRect_le_of_schur_transform (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <= rho := by
  rw [frobNormRect_sylvesterResidualRect_schur_transform m n U R A V S B C Y
    hU hV hA hB]
  exact hres

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9): source-numbered
    alias for exact residual-bound transport from Schur coordinates. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_of_schur_transform :=
  frobNormRect_sylvesterResidualRect_le_of_schur_transform

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    a Frobenius residual-error model in Schur coordinates transfers to the
    original-coordinate computed-residual budget after orthogonal
    reconstruction. -/
theorem sylvesterComputedResidualBudget_of_schur_frobenius_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y RhatS dRs : RMatFn m n) (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hRhatS : forall i j,
      RhatS i j =
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) i j + dRs i j)
    (hrho : 0 <= rho)
    (hdRs : frobNorm dRs <= rho) :
    IsSylvesterComputedResidualBudget m n A B C
      (rectMatMul U (rectMatMul Y (matTranspose V)))
      (rectMatMul U (rectMatMul RhatS (matTranspose V)))
      (fun _ _ => rho) := by
  let Cs : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  let Rs : RMatFn m n := sylvesterResidualRect m n R S Cs Y
  let Xhat : RMatFn m n := rectMatMul U (rectMatMul Y (matTranspose V))
  let Rhat : RMatFn m n := rectMatMul U (rectMatMul RhatS (matTranspose V))
  let dR : RMatFn m n := rectMatMul U (rectMatMul dRs (matTranspose V))
  have hRhatS_fun : RhatS = fun i j => Rs i j + dRs i j := by
    ext i j
    simpa [Rs, Cs] using hRhatS i j
  have hinner :
      rectMatMul RhatS (matTranspose V) =
        fun i j =>
          rectMatMul Rs (matTranspose V) i j +
            rectMatMul dRs (matTranspose V) i j := by
    rw [hRhatS_fun]
    exact rectMatMul_add_left Rs dRs (matTranspose V)
  have houter :
      Rhat =
        fun i j =>
          rectMatMul U (rectMatMul Rs (matTranspose V)) i j + dR i j := by
    unfold Rhat dR
    rw [hinner]
    exact rectMatMul_add_right U
      (rectMatMul Rs (matTranspose V)) (rectMatMul dRs (matTranspose V))
  have horig :
      sylvesterResidualRect m n A B C Xhat =
        rectMatMul U (rectMatMul Rs (matTranspose V)) := by
    simpa [Xhat, Rs, Cs] using
      sylvesterResidualRect_schur_transform_identity
        m n U R A V S B C Y hU hV hA hB
  have hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j := by
    intro i j
    have houterij := congrFun (congrFun houter i) j
    have horigij := congrFun (congrFun horig i) j
    calc
      Rhat i j =
          rectMatMul U (rectMatMul Rs (matTranspose V)) i j + dR i j := houterij
      _ = sylvesterResidualRect m n A B C Xhat i j + dR i j := by
          rw [← horigij]
  have hdR : frobNorm dR <= rho := by
    have hrect : frobNormRect dR = frobNormRect dRs := by
      calc
        frobNormRect dR =
            frobNormRect (rectMatMul dRs (matTranspose V)) := by
            simpa [dR, matMulRectLeft] using
              frobNormRect_orthogonal_left U
                (rectMatMul dRs (matTranspose V)) hU
        _ = frobNormRect dRs := by
            simpa [matMulRectRight] using
              frobNormRect_orthogonal_right dRs (matTranspose V) hV.transpose
    have hnorm : frobNorm dR = frobNorm dRs := by
      rw [← frobNormRect_eq_frobNormFn dR, hrect,
        frobNormRect_eq_frobNormFn dRs]
    simpa [hnorm] using hdRs
  simpa [Xhat, Rhat] using
    sylvesterComputedResidualBudget_of_frobenius_error_model m n
      A B C Xhat Rhat dR rho hRhat hrho hdR

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the Schur-coordinate Frobenius residual-error budget transfer. -/
alias H16_eq16_29_sylvesterComputedResidualBudget_of_schur_frobenius_error_model :=
  sylvesterComputedResidualBudget_of_schur_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    a Schur-coordinate Frobenius residual bound gives an original-coordinate
    computed-residual budget with `Rhat = 0` and uniform radius `rho`. -/
theorem sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y : RMatFn m n) (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    IsSylvesterComputedResidualBudget m n A B C
      (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) := by
  let Xhat : RMatFn m n := rectMatMul U (rectMatMul Y (matTranspose V))
  let Rorig : RMatFn m n := sylvesterResidualRect m n A B C Xhat
  have hres_orig : frobNormRect Rorig <= rho := by
    simpa [Xhat, Rorig] using
      frobNormRect_sylvesterResidualRect_le_of_schur_transform
        m n U R A V S B C Y rho hU hV hA hB hres
  have hrho : 0 <= rho := (frobNormRect_nonneg Rorig).trans hres_orig
  constructor
  · intro _ _
    exact hrho
  · intro i j
    have hentry : |Rorig i j| <= rho :=
      (abs_entry_le_frobNormRect Rorig i j).trans hres_orig
    simpa [Xhat, Rorig] using hentry

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    conservative practical max-entry bound from a Schur-coordinate Frobenius
    residual bound, using `Rhat = 0` and a uniform residual budget `rho`. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (fun _ _ => 0) (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap conservative practical max-entry bound from a Schur-coordinate
    Frobenius residual bound. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent :
      forall p,
        sylvesterPracticalBudgetVec m n PinvAbs
            (fun _ _ => 0) (fun _ _ => rho) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone conservative practical max-entry bound from a Schur-coordinate
    Frobenius residual bound.  This estimator-facing wrapper permits a larger
    supplied inverse/residual budget without proving the estimator itself. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho : Real)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru'
      Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone scalar-cap conservative practical max-entry bound from a
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru'
      Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    practical max-entry bound from a Schur-coordinate Frobenius residual-error
    model.  This wrapper consumes the exact residual-arithmetic certificate and
    does not prove rounded Bartels-Stewart arithmetic. -/
theorem sylvester_practical_error_bound_of_schur_frobenius_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y RhatS dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhatS : forall i j,
      RhatS i j = sylvesterResidualRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Y i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (rectMatMul U (rectMatMul RhatS (matTranspose V)))
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (rectMatMul U (rectMatMul RhatS (matTranspose V)))
      (fun _ _ => rho) Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_schur_frobenius_error_model
        m n U R A V S B C Y RhatS dR rho
        hU hV hA hB hRhatS hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    denominator-free conservative practical max-entry bound from a
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_abs_error_bound_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (fun _ _ => 0) (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap form of the denominator-free conservative Schur residual
    practical max-entry bound. -/
theorem sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent :
      forall p,
        sylvesterPracticalBudgetVec m n PinvAbs
            (fun _ _ => 0) (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the conservative practical wrapper from a Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the scalar-cap conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the monotone conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_mono :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the monotone scalar-cap conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the Schur-coordinate Frobenius residual-error practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_frobenius_error_model :=
  sylvester_practical_error_bound_of_schur_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the denominator-free conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_schur_transform_residual_bound :=
  sylvester_practical_abs_error_bound_of_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the denominator-free scalar-cap Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar :=
  sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    equation-level Schur-coordinate form.  Under supplied orthogonal
    factorizations `A = U R U^T` and `B = V S V^T`, the substitution
    `X = U Y V^T` solves `AX - XB = C` exactly when `Y` solves
    `RY - YS = U^T C V`. -/
theorem sylvester_schur_transform_solution_iff (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul Y (matTranspose V))) <->
      IsSylvesterSolutionRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Y := by
  constructor
  case mp =>
    intro h
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [htrans.symm]
      ext i j
      exact h i j
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      calc
        sylvesterOpRect m n R S Y =
            rectMatMul (matTranspose U)
              (rectMatMul (rectMatMul U
                (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V))) V) := by
                exact (rectMatMul_schur_coords_cancel U V
                  (sylvesterOpRect m n R S Y) hU hV).symm
        _ = rectMatMul (matTranspose U) (rectMatMul C V) := by
                rw [hUMVt]
    intro i j
    exact congrFun (congrFun hM i) j
  case mpr =>
    intro h
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      ext i j
      exact h i j
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [hM]
      exact rectMatMul_schur_coords_expand U V C hU hV
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hsol :
        sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) = C := by
      rw [htrans]
      exact hUMVt
    intro i j
    exact congrFun (congrFun hsol i) j

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    source-numbered alias for the supplied Schur-coordinate equation-level
    solution equivalence. -/
alias H16_eq16_4_5_sylvester_schur_transform_solution_iff :=
  sylvester_schur_transform_solution_iff































/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5), diagonal
    Schur-coordinate case: if supplied orthogonal factors diagonalize `A` and
    `B`, the reconstructed explicit diagonal-coordinate solution solves the
    original Sylvester equation.  This remains an exact-arithmetic conditional
    wrapper; it does not assert Schur existence or floating-point stability. -/
theorem isSylvesterSolutionRect_schurDiagonalSolution (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    IsSylvesterSolutionRect m n A B C
      (sylvesterSchurDiagonalSolution m n U V a b C) := by
  unfold sylvesterSchurDiagonalSolution
  exact
    (sylvester_schur_transform_solution_iff m n
      U (Matrix.diagonal a) A V (Matrix.diagonal b) B C
      (sylvesterDiagonalSolution m n a b
        (rectMatMul (matTranspose U) (rectMatMul C V)))
      hU hV hA hB).mpr
      (isSylvesterSolutionRect_sylvesterDiagonalSolution m n a b
        (rectMatMul (matTranspose U) (rectMatMul C V)) hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), diagonal
    Schur-coordinate case: under supplied orthogonal diagonal factors and
    separated diagonal entries, every original-coordinate solution is the
    reconstructed explicit diagonal-coordinate solution. -/
theorem sylvesterSchurDiagonalSolution_unique (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X) :
    X = sylvesterSchurDiagonalSolution m n U V a b C := by
  let YX : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul X V)
  have hXrecon :
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul YX (matTranspose V))) := by
    dsimp [YX]
    rw [rectMatMul_schur_coords_expand U V X hU hV]
    exact hX
  have hYsol :
      IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b)
        (rectMatMul (matTranspose U) (rectMatMul C V)) YX :=
    (sylvester_schur_transform_solution_iff m n
      U (Matrix.diagonal a) A V (Matrix.diagonal b) B C YX
      hU hV hA hB).mp hXrecon
  have hYeq :
      YX =
        sylvesterDiagonalSolution m n a b
          (rectMatMul (matTranspose U) (rectMatMul C V)) :=
    sylvesterDiagonalSolution_unique m n a b
      (rectMatMul (matTranspose U) (rectMatMul C V)) YX hsep hYsol
  calc
    X = rectMatMul U (rectMatMul YX (matTranspose V)) := by
        dsimp [YX]
        exact (rectMatMul_schur_coords_expand U V X hU hV).symm
    _ = sylvesterSchurDiagonalSolution m n U V a b C := by
        unfold sylvesterSchurDiagonalSolution
        rw [hYeq]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries give a unique exact Sylvester solution. -/
theorem existsUnique_isSylvesterSolutionRect_schurDiagonal (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  refine ⟨sylvesterSchurDiagonalSolution m n U V a b C,
    isSylvesterSolutionRect_schurDiagonalSolution m n U A V B a b C
      hU hV hA hB hsep, ?_⟩
  intro X hX
  exact sylvesterSchurDiagonalSolution_unique m n U A V B a b C X
    hU hV hA hB hsep hX

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient have trivial
    kernel. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 <->
      X = 0 := by
  constructor
  case mp =>
    intro h
    have hsol : IsSylvesterSolutionRect m n A B (0 : RMatFn m n) X :=
      (sylvester_vec_system_iff_solution m n A B (0 : RMatFn m n) X).mp
        (by simpa using h)
    have hX :
        X = sylvesterSchurDiagonalSolution m n U V a b (0 : RMatFn m n) :=
      sylvesterSchurDiagonalSolution_unique m n U A V B a b
        (0 : RMatFn m n) X hU hV hA hB hsep hsol
    rw [hX, sylvesterSchurDiagonalSolution_zero]
  case mpr =>
    intro hX
    rw [hX]
    change Matrix.mulVec (sylvesterVecCoeff m n A B)
        (0 : Prod (Fin n) (Fin m) -> Real) = 0
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient injective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_injective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro x y hxy
  let P := sylvesterVecCoeff m n A B
  have hker : Matrix.mulVec P (x - y) = 0 := by
    dsimp [P]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  obtain ⟨X, hXvec⟩ :=
    Matrix.vec_bijective.surjective (x - y : Prod (Fin n) (Fin m) -> Real)
  have hkerX :
      Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 := by
    dsimp [P] at hker
    rw [hXvec]
    exact hker
  have hXzero : X = 0 :=
    (sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff
      m n U A V B a b X hU hV hA hB hsep).mp hkerX
  have hsub : x - y = 0 := by
    rw [← hXvec, hXzero]
    rfl
  exact sub_eq_zero.mp hsub

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient surjective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_surjective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro y
  obtain ⟨C, hC⟩ := Matrix.vec_bijective.surjective y
  refine ⟨Matrix.vec (sylvesterSchurDiagonalSolution m n U V a b C), ?_⟩
  rw [← hC]
  exact
    (sylvester_vec_system_iff_solution m n A B C
      (sylvesterSchurDiagonalSolution m n U V a b C)).mpr
      (isSylvesterSolutionRect_schurDiagonalSolution
        m n U A V B a b C hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient bijective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_bijective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep,
    sylvesterVecCoeff_schurDiagonal_mulVec_surjective
      m n U A V B a b hU hV hA hB hsep⟩

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vec/Kronecker Sylvester coefficient
    nonsingular. This is the determinant form of the vectorized solve theorem;
    it is a supplied-factor result, not a proof of Schur existence. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  intro hdet
  obtain ⟨x, hxne, hxzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hinj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep
  have hxzero' : x = 0 := by
    apply hinj
    rw [hxzero, Matrix.mulVec_zero]
  exact hxne hxzero'

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: the supplied-factor vectorized Sylvester linear
    system has a unique solution for every vectorized right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_mulVec (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep
  have hsurj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_surjective
      m n U A V B a b hU hV hA hB hsep
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: the practical componentwise error bound can use
    the actual nonsingular inverse of the vec/Kronecker Sylvester coefficient.
    This is an exact supplied-factor subcase; it does not assert Schur
    existence or a floating-point residual computation. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with a monotone estimated practical budget.  The
    exact inverse bound comes from the supplied Schur-diagonal certificate,
    while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise larger
    estimator inputs.  Scope: exact supplied factors only; this does not assert
    Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: a scalar cap on the nonsingular-inverse practical
    budget gives the final practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with a monotone scalar cap on an estimated practical
    budget.  The exact nonsingular inverse is supplied by the Schur-diagonal
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise
    larger estimator inputs.  Scope: exact supplied factors only; this does not
    assert Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form of the practical
    componentwise error bound.  Scope: exact supplied factors only; this does
    not assert Schur existence or a floating-point residual computation. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
      m n U A V B a b C X Xhat Rhat Ru hU hV hA hB hsep hX
      (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with a monotone
    estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hsep hX (And.intro hRu hRhat)
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with a scalar cap
    on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
      m n U A V B a b C X Xhat Rhat Ru eta hU hV hA hB hsep hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with monotone
    supplied estimates and a scalar cap on the estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hsep hX (And.intro hRu hRhat)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model:
    if `Rhat = R(Xhat) + dR` and `|dR| <= Ru`, then the practical
    componentwise error bound follows using the nonsingular inverse of the
    supplied Schur-diagonal vec/Kronecker coefficient. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
      m n U A V B a b C X Xhat Rhat Ru hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a monotone
    estimated practical budget.  This is an exact supplied-factor wrapper: no
    Schur existence, rounded residual arithmetic, or estimator proof is
    asserted. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a scalar
    cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
      m n U A V B a b C X Xhat Rhat Ru eta hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a monotone
    scalar cap on an estimated practical budget.  This remains an exact
    supplied-factor wrapper: no Schur existence, rounded residual arithmetic,
    or estimator proof is asserted. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), square supplied
    diagonal Schur-coordinate case: pairwise spectral-coordinate exclusion
    makes the vec/Kronecker Sylvester coefficient nonsingular.  The positive
    dimension hypothesis keeps this wrapper aligned with the square
    spectral-exclusion endpoints; the proof only needs the equivalent
    subtraction form used by the supplied-factor certificate above. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Matrix.det (sylvesterVecCoeff n n A B) ≠ 0 := by
  have _hn : 0 < n := hn
  have hsep_sub : forall i j, Not (a i - b j = 0) := by
    intro i j hzero
    exact hsep i j (sub_eq_zero.mp hzero)
  exact
    sylvesterVecCoeff_schurDiagonal_det_ne_zero
      n n U A V B a b hU hV hA hB hsep_sub

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square supplied diagonal
    Schur-coordinate case under pairwise spectral-coordinate exclusion:
    the raw computed-residual budget endpoint no longer needs a separately
    supplied determinant or gap certificate.  Scope: exact supplied factors
    only; this does not assert Schur existence or rounded residual arithmetic. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_entrywise_ne_computed_residual_budget
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn n n)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
        n U A V B a b hn hU hV hA hB hsep)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square supplied diagonal
    Schur-coordinate case under pairwise spectral-coordinate exclusion:
    a Frobenius residual-error model supplies the uniform practical residual
    budget, while the spectral exclusion discharges nonsingularity.  Scope:
    exact supplied factors only; this does not assert Schur existence,
    rounded Schur arithmetic, or estimator production. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_entrywise_ne_computed_residual_frobenius_error_model
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
      n A B C X Xhat Rhat dR rho
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
        n U A V B a b hn hU hV hA hB hsep)
      hX hRhat hrho hdR hXhat

-- ============================================================
-- Lyapunov specialization from Chapter 16.3
-- ============================================================











































































































-- ============================================================
-- Separation infimum from Chapter 16.4
-- ============================================================











































































































































































































































































































































































































private theorem sylvesterVecCoeff_det_ne_zero_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    Not ((sylvesterVecCoeff n n A B).det = 0) := by
  classical
  intro hdet
  have hker :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := sylvesterVecCoeff n n A B)).mpr hdet
  cases hker with
  | intro x hx =>
      have hxne := hx.1
      have hxzero := hx.2
      let X : RMatFn n n := fun i j => x (j, i)
      have hvecX : Matrix.vec X = x := by
        ext p
        rfl
      have hXne : Not (frobNormSq X = 0) := by
        intro hsq
        apply hxne
        ext p
        have hfrob0 : frobNorm X = 0 := by
          rw [frobNorm_eq_sqrt_frobNormSq,
            Real.sqrt_eq_zero (frobNormSq_nonneg X)]
          exact hsq
        have hentries := (frobNorm_eq_zero_iff X).mp hfrob0
        cases p with
        | mk j i =>
            simpa [X] using hentries i j
      have hOpZero : sylvesterOp n A B X = 0 := by
        have hxzero' :
            Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec X) = 0 := by
          simpa [hvecX] using hxzero
        have hsyl : IsSylvesterSolutionRect n n A B (0 : RMatFn n n) X :=
          (sylvester_vec_system_iff_solution n n A B (0 : RMatFn n n) X).mp
            (by simpa using hxzero')
        ext i j
        have hrect := hsyl i j
        simpa [sylvesterOpRect_square_eq_sylvesterOp n A B X] using hrect
      have hle := hSep.2 X hXne
      rw [hOpZero] at hle
      have hzero : frobNormSq (0 : RMatFn n n) = 0 := by
        unfold frobNormSq
        simp
      rw [hzero] at hle
      have hXpos : 0 < frobNormSq X :=
        lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hXne)
      have hsig2pos : 0 < sigma ^ 2 := sq_pos_of_pos hSep.1
      exact (not_le_of_gt (mul_pos hsig2pos hXpos)) hle

private theorem sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    Not ((sylvesterVecCoeff n n A B).det = 0) := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square arbitrary-
    coefficient endpoint: a supplied positive `SepLowerBound` certificate
    discharges vec/Kronecker nonsingularity for the practical computed-residual
    certificate. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute endpoint for a practical computed-residual
    certificate.  The source separation certificate discharges vec/Kronecker
    nonsingularity, and no positive `||Xhat||` denominator is needed. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute monotone certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute monotone scalar certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint with monotone supplied inverse and residual
    estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate raw budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate raw budget endpoint with monotone supplied estimates and a
    scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute raw-budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute raw-budget endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for an explicit computed-residual error
    model. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate error-model endpoint with monotone supplied estimates and a
    scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute residual error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute residual error-model endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum lower-bound
    endpoint for the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for a practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute monotone certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute monotone scalar certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum raw
    budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum raw budget
    endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    raw-budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    raw-budget endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    error-model endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    residual error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    residual error-model endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent

-- ============================================================
-- Equation (16.29) source-numbered practical endpoint aliases
-- ============================================================




































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute monotone scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute monotone
    certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute monotone scalar
    certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar raw budget
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar error-model
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar

-- ============================================================
-- Perturbation source wrappers from Chapter 16.3
-- ============================================================





























































































































































































































































































































































-- ============================================================
-- A posteriori source wrapper from Chapter 16.4
-- ============================================================


























































































































































































































































































































-- ============================================================
-- Generalized equations from Chapter 16.5
-- ============================================================




























































































































































































end NumStability
