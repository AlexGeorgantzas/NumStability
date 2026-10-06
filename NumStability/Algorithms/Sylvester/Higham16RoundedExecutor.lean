-- Algorithms/Sylvester/Higham16RoundedExecutor.lean
--
-- Higham, 2nd ed., Chapter 16, pp. 307-308, equations (16.5)-(16.9).
-- This module makes every operation *after supplied Schur factors* literal:
-- the two right-hand-side products, triangular Sylvester solve, and two
-- reconstruction products are all performed through the repository FPModel.
-- Computing the Schur factors themselves remains a separate missing producer;
-- see the Chapter 16 coverage ledger and the source's footnote 13.

import NumStability.Algorithms.MatMul
import NumStability.Algorithms.Sylvester.Higham16Eq9EndToEnd
import NumStability.Algorithms.Sylvester.Higham16QuasiQuasiSylvester

namespace NumStability

open scoped BigOperators

/-- The explicit Frobenius roundoff coefficient for two rounded products
    `fl(L * fl(X * R))` when `L` and `R` are orthogonal.  The inner products
    have lengths `n` and `m`, respectively. -/
noncomputable def orthogonalSandwichRoundoffCoeff
    (fp : FPModel) (m n : Nat) : Real :=
  gamma fp m * Real.sqrt (m : Real) *
      (1 + gamma fp n * Real.sqrt (n : Real)) +
    gamma fp n * Real.sqrt (n : Real)

theorem orthogonalSandwichRoundoffCoeff_nonneg
    (fp : FPModel) (m n : Nat)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n) :
    0 <= orthogonalSandwichRoundoffCoeff fp m n := by
  unfold orthogonalSandwichRoundoffCoeff
  have hgm0 : 0 <= gamma fp m := gamma_nonneg fp hgm
  have hgn0 : 0 <= gamma fp n := gamma_nonneg fp hgn
  have hsm : 0 <= Real.sqrt (m : Real) := Real.sqrt_nonneg _
  have hsn : 0 <= Real.sqrt (n : Real) := Real.sqrt_nonneg _
  exact add_nonneg
    (mul_nonneg (mul_nonneg hgm0 hsm)
      (add_nonneg zero_le_one (mul_nonneg hgn0 hsn)))
    (mul_nonneg hgn0 hsn)

/-- Algebraic absorption used to turn the literal rounded-executor estimate
    into the printed `(data norm) * (computed solution norm)` scale.  The
    factor `(1 - tau)^2` accounts for using the rounded reconstruction twice:
    once to compare its exact-coordinate norm with the computed norm, and once
    to absorb the occurrence of the residual inside the bound for `||C||`. -/
theorem roundedSylvesterResidual_absorb
    (r d x y c g tau : Real)
    (hd : 0 <= d) (hg : 0 <= g) (htau : 0 <= tau) (htau1 : tau < 1)
    (hyx : (1 - tau) * y <= x)
    (hcr : c <= r + d * x)
    (hpre :
      r <= g * d * (x + tau * y) + tau * c + d * (tau * y)) :
    r <= ((g + 2 * tau - tau ^ 2) / (1 - tau) ^ 2) * d * x := by
  have hone : 0 <= 1 - tau := sub_nonneg.mpr (le_of_lt htau1)
  have htauc := mul_le_mul_of_nonneg_left hcr htau
  have habsorb :
      (1 - tau) * r <=
        g * d * (x + tau * y) + tau * d * x + d * (tau * y) := by
    nlinarith
  have habsorbMul := mul_le_mul_of_nonneg_left habsorb hone
  have htyx := mul_le_mul_of_nonneg_left hyx htau
  have hshape : (1 - tau) * (x + tau * y) <= x := by
    nlinarith
  have hgd : 0 <= g * d := mul_nonneg hg hd
  have hgshape := mul_le_mul_of_nonneg_left hshape hgd
  have htaud : 0 <= tau * d := mul_nonneg htau hd
  have hdy := mul_le_mul_of_nonneg_left hyx htaud
  have hscaled :
      (1 - tau) ^ 2 * r <= (g + 2 * tau - tau ^ 2) * d * x := by
    nlinarith
  have hden : 0 < (1 - tau) ^ 2 := sq_pos_of_pos (sub_pos.mpr htau1)
  calc
    r <= ((g + 2 * tau - tau ^ 2) * d * x) / (1 - tau) ^ 2 :=
      (le_div_iff₀ hden).2
        (by simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hscaled)
    _ = ((g + 2 * tau - tau ^ 2) / (1 - tau) ^ 2) * d * x := by
      ring

/-- Matrix-level wrapper around `roundedSylvesterResidual_absorb`.  It
    discharges the two geometric facts used by the absorption: orthogonal
    reconstruction gives `(1-tau)||Y|| <= ||Xhat||`, and the residual
    identity gives `||C|| <= ||residual|| + (||A||+||B||)||Xhat||`. -/
theorem roundedSylvesterResidual_computedScale_of_prebound
    (m n : Nat) (U : RMatFn m m) (V : RMatFn n n)
    (A : RMatFn m m) (B : RMatFn n n) (C Y Xhat : RMatFn m n)
    (g tau : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hg : 0 <= g) (htau0 : 0 <= tau) (htau1 : tau < 1)
    (hXerr :
      frobNormRect
          (fun i j =>
            Xhat i j -
              rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
        tau * frobNormRect Y)
    (hpre :
      frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
        g * (frobNormRect A + frobNormRect B) *
            (frobNormRect Xhat + tau * frobNormRect Y) +
          tau * frobNormRect C +
          (frobNormRect A + frobNormRect B) *
            (tau * frobNormRect Y)) :
    frobNormRect (sylvesterResidualRect m n A B C Xhat) <=
      ((g + 2 * tau - tau ^ 2) / (1 - tau) ^ 2) *
        (frobNormRect A + frobNormRect B) * frobNormRect Xhat := by
  let r := frobNormRect (sylvesterResidualRect m n A B C Xhat)
  let d := frobNormRect A + frobNormRect B
  let x := frobNormRect Xhat
  let y := frobNormRect Y
  let c := frobNormRect C
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
  have hop : frobNormRect (sylvesterOpRect m n A B Xhat) <= d * x := by
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
  have hCsplit : c <= r + frobNormRect (sylvesterOpRect m n A B Xhat) := by
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
  have hpre' : r <= g * d * (x + tau * y) + tau * c + d * (tau * y) := by
    simpa only [r, d, x, y, c] using hpre
  simpa only [r, d, x, y, c] using
    roundedSylvesterResidual_absorb r d x y c g tau
      (add_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B))
      hg htau0 htau1 hyx hcr hpre'

/-- A literal two-product floating-point orthogonal sandwich.  The right
    product is formed first, matching `U * (X * V)` in the Schur formulas. -/
noncomputable def flOrthogonalSandwich (fp : FPModel) (m n : Nat)
    (L : RMatFn m m) (X : RMatFn m n) (R : RMatFn n n) : RMatFn m n :=
  fl_matMul fp m m n L (fl_matMul fp m n n X R)

/-- Higham, 2nd ed., Chapter 16, equations (16.5) and (16.9): both matrix
    products in an orthogonal sandwich are rounded, with no supplied transform
    error budget. -/
theorem flOrthogonalSandwich_frobNormRect_error_bound
    (fp : FPModel) (m n : Nat)
    (L : RMatFn m m) (X : RMatFn m n) (R : RMatFn n n)
    (hL : IsOrthogonal m L) (hR : IsOrthogonal n R)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n) :
    frobNormRect
        (fun i j =>
          flOrthogonalSandwich fp m n L X R i j -
            rectMatMul L (rectMatMul X R) i j) <=
      orthogonalSandwichRoundoffCoeff fp m n * frobNormRect X := by
  let XRhat : RMatFn m n := fl_matMul fp m n n X R
  let XR : RMatFn m n := rectMatMul X R
  let Yhat : RMatFn m n := fl_matMul fp m m n L XRhat
  have hLn : frobNormRect L = Real.sqrt (m : Real) := by
    rw [frobNormRect_eq_frobNorm]
    exact hL.frobNorm_eq_sqrt_card
  have hRn : frobNormRect R = Real.sqrt (n : Real) := by
    rw [frobNormRect_eq_frobNorm]
    exact hR.frobNorm_eq_sqrt_card
  have hXR :
      frobNormRect (fun i j => XRhat i j - XR i j) <=
        gamma fp n * frobNormRect X * frobNormRect R := by
    simpa [XRhat, XR, rectMatMul] using
      matMul_error_bound_frobNormRect fp m n n X R hgn
  have hXRexact : frobNormRect XR = frobNormRect X := by
    exact frobNormRect_orthogonal_right X R hR
  have hXRhat :
      frobNormRect XRhat <=
        (1 + gamma fp n * Real.sqrt (n : Real)) * frobNormRect X := by
    calc
      frobNormRect XRhat =
          frobNormRect (fun i j => (XRhat i j - XR i j) + XR i j) := by
            congr 1
            ext i j
            ring
      _ <= frobNormRect (fun i j => XRhat i j - XR i j) +
          frobNormRect XR :=
            frobNormRect_add_le (fun i j => XRhat i j - XR i j) XR
      _ <= gamma fp n * frobNormRect X * frobNormRect R +
          frobNormRect X := by
            exact add_le_add hXR (le_of_eq hXRexact)
      _ = (1 + gamma fp n * Real.sqrt (n : Real)) *
          frobNormRect X := by rw [hRn]; ring
  have hY :
      frobNormRect
          (fun i j => Yhat i j - rectMatMul L XRhat i j) <=
        gamma fp m * frobNormRect L * frobNormRect XRhat := by
    simpa [Yhat, rectMatMul] using
      matMul_error_bound_frobNormRect fp m m n L XRhat hgm
  have hprop :
      frobNormRect
          (rectMatMul L (fun i j => XRhat i j - XR i j)) =
        frobNormRect (fun i j => XRhat i j - XR i j) :=
    frobNormRect_orthogonal_left L (fun i j => XRhat i j - XR i j) hL
  have hsplit :
      (fun i j => Yhat i j - rectMatMul L XR i j) =
        fun i j =>
          (Yhat i j - rectMatMul L XRhat i j) +
            rectMatMul L (fun a b => XRhat a b - XR a b) i j := by
    ext i j
    unfold rectMatMul
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  calc
    frobNormRect
        (fun i j =>
          flOrthogonalSandwich fp m n L X R i j -
            rectMatMul L (rectMatMul X R) i j) =
      frobNormRect (fun i j => Yhat i j - rectMatMul L XR i j) := by
        rfl
    _ = frobNormRect
        (fun i j =>
          (Yhat i j - rectMatMul L XRhat i j) +
            rectMatMul L (fun a b => XRhat a b - XR a b) i j) := by
          rw [hsplit]
    _ <= frobNormRect
          (fun i j => Yhat i j - rectMatMul L XRhat i j) +
        frobNormRect
          (rectMatMul L (fun a b => XRhat a b - XR a b)) :=
            frobNormRect_add_le _ _
    _ <= gamma fp m * frobNormRect L * frobNormRect XRhat +
        frobNormRect (fun a b => XRhat a b - XR a b) := by
          rw [hprop]
          exact add_le_add hY (le_refl _)
    _ <= gamma fp m * Real.sqrt (m : Real) *
          ((1 + gamma fp n * Real.sqrt (n : Real)) * frobNormRect X) +
        gamma fp n * frobNormRect X * Real.sqrt (n : Real) := by
          rw [hLn]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hXRhat
              (mul_nonneg (gamma_nonneg fp hgm) (Real.sqrt_nonneg _)))
            (by simpa [hRn] using hXR)
    _ = orthogonalSandwichRoundoffCoeff fp m n * frobNormRect X := by
          unfold orthogonalSandwichRoundoffCoeff
          ring

/-- The actually rounded formation `Dhat = fl(U^T * fl(C * V))`. -/
noncomputable def flSylvesterSchurRhsTransform (fp : FPModel) (m n : Nat)
    (U : RMatFn m m) (C : RMatFn m n) (V : RMatFn n n) : RMatFn m n :=
  flOrthogonalSandwich fp m n (matTranspose U) C V

/-- The actually rounded reconstruction `Xhat = fl(U * fl(Y * V^T))`. -/
noncomputable def flSylvesterSchurReconstruct (fp : FPModel) (m n : Nat)
    (U : RMatFn m m) (Y : RMatFn m n) (V : RMatFn n n) : RMatFn m n :=
  flOrthogonalSandwich fp m n U Y (matTranspose V)

/-- Rounded right-hand-side transform error, derived directly from the two
    matrix multiplications rather than supplied as a budget. -/
theorem flSylvesterSchurRhsTransform_error_bound
    (fp : FPModel) (m n : Nat)
    (U : RMatFn m m) (C : RMatFn m n) (V : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n) :
    frobNormRect
        (fun i j =>
          flSylvesterSchurRhsTransform fp m n U C V i j -
            rectMatMul (matTranspose U) (rectMatMul C V) i j) <=
      orthogonalSandwichRoundoffCoeff fp m n * frobNormRect C := by
  exact flOrthogonalSandwich_frobNormRect_error_bound fp m n
    (matTranspose U) C V hU.transpose hV hgm hgn

/-- Rounded reconstruction error, derived directly from the two matrix
    multiplications rather than supplied as a budget. -/
theorem flSylvesterSchurReconstruct_error_bound
    (fp : FPModel) (m n : Nat)
    (U : RMatFn m m) (Y : RMatFn m n) (V : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hgm : gammaValid fp m) (hgn : gammaValid fp n) :
    frobNormRect
        (fun i j =>
          flSylvesterSchurReconstruct fp m n U Y V i j -
            rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      orthogonalSandwichRoundoffCoeff fp m n * frobNormRect Y := by
  exact flOrthogonalSandwich_frobNormRect_error_bound fp m n
    U Y (matTranspose V) hU hV.transpose hgm hgn

/-- The rounded triangular Schur-coordinate solution using the actually
    rounded right-hand-side transform. -/
noncomputable def flBartelsStewartSuppliedSchurCoordinates
    (fp : FPModel) (m n : Nat)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) : RMatFn m n :=
  Wave14.flSylvesterSchurBackSubSolve fp m n R S
    (flSylvesterSchurRhsTransform fp m n U C V)

/-- A literal rounded Bartels-Stewart executor after supplied exact triangular
    Schur factors: both transforms and the triangular solve use `FPModel`. -/
noncomputable def flBartelsStewartSuppliedSchurRounded
    (fp : FPModel) (m n : Nat)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) : RMatFn m n :=
  flSylvesterSchurReconstruct fp m n U
    (flBartelsStewartSuppliedSchurCoordinates fp m n U R V S C) V

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

/-- The explicit coefficient multiplying the data/solution scale in the
    absorbed form of (16.9) for the fully rounded post-factor executor. -/
noncomputable def roundedBartelsStewartResidualCoeff
    (fp : FPModel) (m n : Nat) : Real :=
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  (gamma fp (n * m) + 2 * tau - tau ^ 2) / (1 - tau) ^ 2

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

/-- The rounded quasi/quasi Schur-coordinate solve on the actually rounded
    transformed right-hand side.  This is the general real-Schur counterpart
    of `flBartelsStewartSuppliedSchurCoordinates`; its diagonal systems have
    order one, two, or four and are solved by the repository's rounded GE
    kernel. -/
noncomputable def flBartelsStewartSuppliedRealSchurCoordinates
    (fp : FPModel) (m n : Nat)
    (dblR : Fin m -> Bool) (dblS : Fin n -> Bool)
    (hSp : Wave15.IsQuasiBlockPairing n dblS)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) : RMatFn m n :=
  Wave16.flSylvesterQQBlockBackSubSolve fp m n dblR dblS hSp R S
    (flSylvesterSchurRhsTransform fp m n U C V)

/-- Literal rounded Bartels--Stewart execution after supplied exact real
    Schur factors: rounded RHS transform, rounded 1/2/4-block solve, and
    rounded reconstruction. -/
noncomputable def flBartelsStewartSuppliedRealSchurRounded
    (fp : FPModel) (m n : Nat)
    (dblR : Fin m -> Bool) (dblS : Fin n -> Bool)
    (hSp : Wave15.IsQuasiBlockPairing n dblS)
    (U R : RMatFn m m) (V S : RMatFn n n) (C : RMatFn m n) : RMatFn m n :=
  flSylvesterSchurReconstruct fp m n U
    (flBartelsStewartSuppliedRealSchurCoordinates
      fp m n dblR dblS hSp U R V S C) V

/-- Frobenius form of the already proved fully quasi/quasi componentwise
    (16.8) endpoint. -/
theorem frobNormRect_sylvesterResidualRect_quasiQuasi_backSub_le
    (fp : FPModel) (m n : Nat)
    (dblR : Fin m -> Bool) (dblS : Fin n -> Bool)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) (rho : Real)
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
    (hgv : gammaValid fp (n * m + 20)) :
    frobNormRect
        (sylvesterResidualRect m n R S Ct
          (Wave16.flSylvesterQQBlockBackSubSolve
            fp m n dblR dblS hSp R S Ct)) <=
      ((1 + rho) * gamma fp (n * m + 20)) *
        (frobNormRect R + frobNormRect S) *
        frobNormRect
          (Wave16.flSylvesterQQBlockBackSubSolve
            fp m n dblR dblS hSp R S Ct) := by
  apply Wave14.frobNormRect_le_gamma_dataScale_of_componentwise_product_budget
  · exact mul_nonneg (by linarith) (gamma_nonneg fp hgv)
  · intro i k
    exact Wave16.sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le
      fp m n dblR dblS R S Ct rho hRp hSp hR hS hpiv hrho hgrow hgv i k

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

/-- Explicit (16.9) coefficient for the general real-Schur post-factor
    executor. -/
noncomputable def roundedRealSchurBartelsStewartResidualCoeff
    (fp : FPModel) (m n : Nat) (rho : Real) : Real :=
  let tau := orthogonalSandwichRoundoffCoeff fp m n
  let g := (1 + rho) * gamma fp (n * m + 20)
  (g + 2 * tau - tau ^ 2) / (1 - tau) ^ 2

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
