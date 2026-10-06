import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.Executor
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiQuasiSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.SmallSystemRounding
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.EndToEnd
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.ResidualAssembly
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equation09.Assembly

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.RoundedExecutor

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16RoundedExecutor.lean
--
-- Higham, 2nd ed., Chapter 16, pp. 307-308, equations (16.5)-(16.9).
-- This module makes every operation *after supplied Schur factors* literal:
-- the two right-hand-side products, triangular Sylvester solve, and two
-- reconstruction products are all performed through the repository FPModel.
-- Computing the Schur factors themselves remains a separate missing producer;
-- see the Chapter 16 coverage ledger and the source's footnote 13.





namespace NumStability

open scoped BigOperators





















































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16, p. 308, equation (16.9), strongest direct
    pre-absorption bound for the literal rounded executor with supplied exact
    triangular Schur factors.  No transform, reconstruction, or solve residual
    budget is assumed: all three are discharged from the concrete algorithms. -/
theorem flBartelsStewartSuppliedSchurRounded_residual_bound
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R)
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) ≠ 0)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n)
    (hgsolve : gammaValid fp (n * m)) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (flBartelsStewartSuppliedSchurRounded fp m n U R V S C)) <=
      gamma fp (n * m) * (frobNormRect A + frobNormRect B) *
          (frobNormRect (flBartelsStewartSuppliedSchurRounded fp m n U R V S C) +
            orthogonalSandwichRoundoffCoeff fp m n *
              frobNormRect
                (flBartelsStewartSuppliedSchurCoordinates fp m n U R V S C)) +
        orthogonalSandwichRoundoffCoeff fp m n * frobNormRect C +
        (frobNormRect A + frobNormRect B) *
          (orthogonalSandwichRoundoffCoeff fp m n *
            frobNormRect
              (flBartelsStewartSuppliedSchurCoordinates fp m n U R V S C)) := by
  let Dhat := flSylvesterSchurRhsTransform fp m n U C V
  let Y := flBartelsStewartSuppliedSchurCoordinates fp m n U R V S C
  let Xhat := flBartelsStewartSuppliedSchurRounded fp m n U R V S C
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  have hDhat :
      frobNormRect
          (fun i j => Dhat i j -
            rectMatMul (matTranspose U) (rectMatMul C V) i j) <=
        tau * frobNormRect C := by
    simpa [Dhat, tau] using
      flSylvesterSchurRhsTransform_error_bound fp m n U C V
        hU hV hgm hgn
  have hXhat :
      frobNormRect
          (fun i j => Xhat i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
        tau * frobNormRect Y := by
    simpa [Xhat, tau, flBartelsStewartSuppliedSchurRounded] using
      flSylvesterSchurReconstruct_error_bound fp m n U Y V
        hU hV hgm hgn
  have hres :
      frobNormRect (sylvesterResidualRect m n R S Dhat Y) <=
        gamma fp (n * m) * (frobNormRect R + frobNormRect S) *
          frobNormRect Y := by
    simpa [Dhat, Y, flBartelsStewartSuppliedSchurCoordinates] using
      Wave14.frobNormRect_sylvesterResidualRect_schurTriangular_backSub_le
        fp m n U R A V S B Dhat hU hV hA hB hR hS hshift hgsolve
  have hbase :=
    Wave14.frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets
      m n U R A V S B C Y Dhat Xhat (gamma fp (n * m))
        (tau * frobNormRect C) (tau * frobNormRect Y)
        hU hV hA hB (gamma_nonneg fp hgsolve) hDhat hXhat hres
  simpa [Dhat, Y, Xhat, tau] using hbase








/-- Higham, 2nd ed., Chapter 16, p. 308, equation (16.9): literal rounded
    post-factor Bartels--Stewart execution, in the printed residual scale.

    The Schur factors are exact supplied inputs.  Every operation after those
    inputs is an `FPModel` operation, and the result assumes no
    target-equivalent transform, solve, or reconstruction error budget.  The
    smallness hypothesis is the explicit condition needed to absorb the two
    rounded orthogonal sandwiches. -/
theorem flBartelsStewartSuppliedSchurRounded_residual_bound_computedScale
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperTriangularFn m R)
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) ≠ 0)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n)
    (hgsolve : gammaValid fp (n * m))
    (htau : orthogonalSandwichRoundoffCoeff fp m n < 1) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (flBartelsStewartSuppliedSchurRounded fp m n U R V S C)) <=
      roundedBartelsStewartResidualCoeff fp m n *
        (frobNormRect A + frobNormRect B) *
        frobNormRect
          (flBartelsStewartSuppliedSchurRounded fp m n U R V S C) := by
  let Y := flBartelsStewartSuppliedSchurCoordinates fp m n U R V S C
  let Xhat := flBartelsStewartSuppliedSchurRounded fp m n U R V S C
  let r := frobNormRect (sylvesterResidualRect m n A B C Xhat)
  let d := frobNormRect A + frobNormRect B
  let x := frobNormRect Xhat
  let y := frobNormRect Y
  let c := frobNormRect C
  let g := gamma fp (n * m)
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  have hpre :
      r <= g * d * (x + tau * y) + tau * c + d * (tau * y) := by
    simpa [r, d, x, y, c, g, tau, Xhat, Y] using
      flBartelsStewartSuppliedSchurRounded_residual_bound
        fp m n U R A V S B C hU hV hA hB hR hS hshift hgm hgn hgsolve
  have htau0 : 0 <= tau := by
    exact orthogonalSandwichRoundoffCoeff_nonneg fp m n hgm hgn
  have hXerr :
      frobNormRect
          (fun i j =>
            Xhat i j -
              rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
        tau * y := by
    simpa [Xhat, Y, tau, y, flBartelsStewartSuppliedSchurRounded] using
      flSylvesterSchurReconstruct_error_bound fp m n U Y V
        hU hV hgm hgn
  have hy_le : y <= x + tau * y := by
    have horth :
        frobNormRect Y =
          frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) :=
      (Wave14.frobNormRect_orthogonal_conjugation_eq U Y V hU hV).symm
    have htri :
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) <=
          frobNormRect Xhat +
            frobNormRect
              (fun i j =>
                Xhat i j -
                  rectMatMul U (rectMatMul Y (matTranspose V)) i j) := by
      calc
        frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) =
            frobNormRect
              (fun i j =>
                Xhat i j -
                  (Xhat i j -
                    rectMatMul U (rectMatMul Y (matTranspose V)) i j)) := by
              congr 1
              ext i j
              ring
        _ <= frobNormRect Xhat +
              frobNormRect
                (fun i j =>
                  Xhat i j -
                    rectMatMul U (rectMatMul Y (matTranspose V)) i j) :=
            frobNormRect_sub_le Xhat
              (fun i j =>
                Xhat i j -
                  rectMatMul U (rectMatMul Y (matTranspose V)) i j)
    calc
      y = frobNormRect Y := rfl
      _ = frobNormRect (rectMatMul U (rectMatMul Y (matTranspose V))) := horth
      _ <= frobNormRect Xhat +
            frobNormRect
              (fun i j =>
                Xhat i j -
                  rectMatMul U (rectMatMul Y (matTranspose V)) i j) := htri
      _ <= x + tau * y := by
        simpa only [x, y] using add_le_add (le_refl (frobNormRect Xhat)) hXerr
  have hyx : (1 - tau) * y <= x := by
    nlinarith
  have hop :
      frobNormRect (sylvesterOpRect m n A B Xhat) <= d * x := by
    change
      frobNormRect
          (fun i j => rectMatMul A Xhat i j - rectMatMul Xhat B i j) <=
        d * x
    calc
      frobNormRect
          (fun i j => rectMatMul A Xhat i j - rectMatMul Xhat B i j) <=
          frobNormRect (rectMatMul A Xhat) +
            frobNormRect (rectMatMul Xhat B) :=
        frobNormRect_sub_le (rectMatMul A Xhat) (rectMatMul Xhat B)
      _ <= frobNormRect A * frobNormRect Xhat +
            frobNormRect Xhat * frobNormRect B :=
        add_le_add
          (frobNormRect_rectMatMul_le A Xhat)
          (frobNormRect_rectMatMul_le Xhat B)
      _ = d * x := by
        simp only [d, x]
        ring
  have hCsplit :
      c <= r + frobNormRect (sylvesterOpRect m n A B Xhat) := by
    calc
      c = frobNormRect
          (fun i j =>
            sylvesterResidualRect m n A B C Xhat i j +
              sylvesterOpRect m n A B Xhat i j) := by
            simp only [c, sylvesterResidualRect]
            congr 1
            ext i j
            ring
      _ <= r + frobNormRect (sylvesterOpRect m n A B Xhat) := by
        simpa only [r] using
          frobNormRect_add_le
            (sylvesterResidualRect m n A B C Xhat)
            (sylvesterOpRect m n A B Xhat)
  have hcr : c <= r + d * x :=
    le_trans hCsplit (add_le_add (le_refl r) hop)
  have hfinal := roundedSylvesterResidual_absorb r d x y c g tau
    (add_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B))
    (gamma_nonneg fp hgsolve) htau0 (by simpa [tau] using htau)
    hyx hcr hpre
  simpa [r, d, x, y, c, g, tau, Xhat, Y,
    roundedBartelsStewartResidualCoeff] using hfinal

/-- Source-numbered name for the literal post-factor (16.9) endpoint. -/
alias H16_eq16_9_flBartelsStewartSuppliedSchurRounded_residual_bound :=
  flBartelsStewartSuppliedSchurRounded_residual_bound_computedScale

-- ============================================================
-- Fully real-Schur (quasi/quasi) post-factor executor
-- ============================================================



































































/-- Pre-absorption (16.9) for the literal rounded real-Schur executor.  No
    transform, solve, or reconstruction budget is supplied by the caller. -/
theorem flBartelsStewartSuppliedRealSchurRounded_residual_bound
    (fp : FPModel) (m n : Nat)
    (dblR : Fin m -> Bool) (dblS : Fin n -> Bool)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hRp : Wave15.IsQuasiBlockPairing m dblR)
    (hSp : Wave15.IsQuasiBlockPairing n dblS)
    (hR : Wave15.IsQuasiUpperTriangularFn m R dblR)
    (hS : Wave15.IsQuasiUpperTriangularFn n S dblS)
    (hpiv : forall a : Fin (n * m),
      Wave16.flGEPivots fp
        (Wave16.sylvesterQQBe m n dblR dblS hSp a -
          Wave16.sylvesterQQBs m n dblR dblS hSp a - 1)
        (Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hrho : 0 <= rho)
    (hgrow : forall (a : Fin (n * m))
      (u v : Fin (Wave16.sylvesterQQBe m n dblR dblS hSp a -
        Wave16.sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      Wave16.flGEBudget fp
          (Wave16.sylvesterQQBe m n dblR dblS hSp a -
            Wave16.sylvesterQQBs m n dblR dblS hSp a - 1)
          (Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v <=
        (1 + rho) *
          |Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n)
    (hgv : gammaValid fp (n * m + 20)) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (flBartelsStewartSuppliedRealSchurRounded
            fp m n dblR dblS hSp U R V S C)) <=
      ((1 + rho) * gamma fp (n * m + 20)) *
          (frobNormRect A + frobNormRect B) *
          (frobNormRect
              (flBartelsStewartSuppliedRealSchurRounded
                fp m n dblR dblS hSp U R V S C) +
            orthogonalSandwichRoundoffCoeff fp m n *
              frobNormRect
                (flBartelsStewartSuppliedRealSchurCoordinates
                  fp m n dblR dblS hSp U R V S C)) +
        orthogonalSandwichRoundoffCoeff fp m n * frobNormRect C +
        (frobNormRect A + frobNormRect B) *
          (orthogonalSandwichRoundoffCoeff fp m n *
            frobNormRect
              (flBartelsStewartSuppliedRealSchurCoordinates
                fp m n dblR dblS hSp U R V S C)) := by
  let Dhat := flSylvesterSchurRhsTransform fp m n U C V
  let Y := flBartelsStewartSuppliedRealSchurCoordinates
    fp m n dblR dblS hSp U R V S C
  let Xhat := flBartelsStewartSuppliedRealSchurRounded
    fp m n dblR dblS hSp U R V S C
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  let g := (1 + rho) * gamma fp (n * m + 20)
  have hDhat :
      frobNormRect
          (fun i j => Dhat i j -
            rectMatMul (matTranspose U) (rectMatMul C V) i j) <=
        tau * frobNormRect C := by
    simpa [Dhat, tau] using
      flSylvesterSchurRhsTransform_error_bound fp m n U C V
        hU hV hgm hgn
  have hXhat :
      frobNormRect
          (fun i j => Xhat i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
        tau * frobNormRect Y := by
    simpa [Xhat, Y, tau, flBartelsStewartSuppliedRealSchurRounded] using
      flSylvesterSchurReconstruct_error_bound fp m n U Y V
        hU hV hgm hgn
  have hres :
      frobNormRect (sylvesterResidualRect m n R S Dhat Y) <=
        g * (frobNormRect R + frobNormRect S) * frobNormRect Y := by
    simpa [Dhat, Y, g, flBartelsStewartSuppliedRealSchurCoordinates] using
      frobNormRect_sylvesterResidualRect_quasiQuasi_backSub_le
        fp m n dblR dblS R S Dhat rho hRp hSp hR hS hpiv hrho hgrow hgv
  have hbase :=
    Wave14.frobNormRect_sylvesterResidualRect_le_computedScale_of_schur_residual_with_transform_budgets
      m n U R A V S B C Y Dhat Xhat g
        (tau * frobNormRect C) (tau * frobNormRect Y)
        hU hV hA hB (mul_nonneg (by linarith) (gamma_nonneg fp hgv))
        hDhat hXhat hres
  simpa [Dhat, Y, Xhat, tau, g] using hbase









/-- Higham (16.9), general real-Schur form: after supplied exact orthogonal
    quasi-Schur factors, the entire remaining Bartels--Stewart computation is
    literal rounded arithmetic and satisfies the printed data/solution-scale
    residual bound. -/
theorem flBartelsStewartSuppliedRealSchurRounded_residual_bound_computedScale
    (fp : FPModel) (m n : Nat)
    (dblR : Fin m -> Bool) (dblS : Fin n -> Bool)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hRp : Wave15.IsQuasiBlockPairing m dblR)
    (hSp : Wave15.IsQuasiBlockPairing n dblS)
    (hR : Wave15.IsQuasiUpperTriangularFn m R dblR)
    (hS : Wave15.IsQuasiUpperTriangularFn n S dblS)
    (hpiv : forall a : Fin (n * m),
      Wave16.flGEPivots fp
        (Wave16.sylvesterQQBe m n dblR dblS hSp a -
          Wave16.sylvesterQQBs m n dblR dblS hSp a - 1)
        (Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a))
    (hrho : 0 <= rho)
    (hgrow : forall (a : Fin (n * m))
      (u v : Fin (Wave16.sylvesterQQBe m n dblR dblS hSp a -
        Wave16.sylvesterQQBs m n dblR dblS hSp a - 1 + 1)),
      Wave16.flGEBudget fp
          (Wave16.sylvesterQQBe m n dblR dblS hSp a -
            Wave16.sylvesterQQBs m n dblR dblS hSp a - 1)
          (Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a) u v <=
        (1 + rho) *
          |Wave16.sylvesterQQDiagBlock m n dblR dblS hSp R S a u v|)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n)
    (hgv : gammaValid fp (n * m + 20))
    (htau : orthogonalSandwichRoundoffCoeff fp m n < 1) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (flBartelsStewartSuppliedRealSchurRounded
            fp m n dblR dblS hSp U R V S C)) <=
      roundedRealSchurBartelsStewartResidualCoeff fp m n rho *
        (frobNormRect A + frobNormRect B) *
        frobNormRect
          (flBartelsStewartSuppliedRealSchurRounded
            fp m n dblR dblS hSp U R V S C) := by
  let Y := flBartelsStewartSuppliedRealSchurCoordinates
    fp m n dblR dblS hSp U R V S C
  let Xhat := flBartelsStewartSuppliedRealSchurRounded
    fp m n dblR dblS hSp U R V S C
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  let g := (1 + rho) * gamma fp (n * m + 20)
  have hpre :
      frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
        g * (frobNormRect A + frobNormRect B) *
            (frobNormRect Xhat + tau * frobNormRect Y) +
          tau * frobNormRect C +
          (frobNormRect A + frobNormRect B) *
            (tau * frobNormRect Y) := by
    simpa [Xhat, Y, tau, g] using
      flBartelsStewartSuppliedRealSchurRounded_residual_bound
        fp m n dblR dblS U R A V S B C rho hU hV hA hB
        hRp hSp hR hS hpiv hrho hgrow hgm hgn hgv
  have hXerr :
      frobNormRect
          (fun i j => Xhat i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
        tau * frobNormRect Y := by
    simpa [Xhat, Y, tau, flBartelsStewartSuppliedRealSchurRounded] using
      flSylvesterSchurReconstruct_error_bound fp m n U Y V hU hV hgm hgn
  have hfinal := roundedSylvesterResidual_computedScale_of_prebound
    m n U V A B C Y Xhat g tau hU hV
    (mul_nonneg (by linarith) (gamma_nonneg fp hgv))
    (orthogonalSandwichRoundoffCoeff_nonneg fp m n hgm hgn)
    (by simpa [tau] using htau) hXerr hpre
  simpa [Xhat, Y, tau, g, roundedRealSchurBartelsStewartResidualCoeff]
    using hfinal

/-- Source-numbered name for the literal general-real-Schur (16.9) endpoint. -/
alias H16_eq16_9_flBartelsStewartSuppliedRealSchurRounded_residual_bound :=
  flBartelsStewartSuppliedRealSchurRounded_residual_bound_computedScale

end NumStability
