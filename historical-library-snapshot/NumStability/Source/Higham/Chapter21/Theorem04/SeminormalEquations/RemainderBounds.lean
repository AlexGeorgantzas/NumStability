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
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.RemainderBounds
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.ActualOutput
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Signed

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.RemainderBounds

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Uniform local bounds for the signed SNE higher-order terms.



namespace NumStability

open scoped BigOperators

set_option maxHeartbeats 1200000

/-- Explicit radius-uniform bound for the difference between the exact
QR-reference dual vector and the result of the two perturbed triangular
factors.

This is obtained from the exact Demmel--Higham factor identity.  It assumes
only the two componentwise triangular-solve certificates and a fixed upper
radius for their common coefficient; no forward-error conclusion is supplied
as a premise. -/
theorem higham21_dh1993_factor_difference_vecNorm2_le_radius
    {m : Nat}
    (theta radius : Real)
    (htheta : 0 <= theta) (htheta_radius : theta <= radius)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat : Fin m -> Real)
    (hInv : IsInverse m R Rinv)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat))
    (hDeltaR1 : forall i j, |DeltaR1 i j| <= theta * |R i j|)
    (hDeltaR2 : forall i j, |DeltaR2 i j| <= theta * |R i j|) :
    vecNorm2 (fun i => ybar i - yhat i) <=
      theta *
        (frobNorm Rinv *
          (frobNorm R +
            frobNorm Rinv * frobNorm R *
              (frobNorm R + radius * frobNorm R)) *
          vecNorm2 yhat) := by
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let R2 : Fin m -> Fin m -> Real := fun i j => R i j + DeltaR2 i j
  let v2 : Fin m -> Real := rectMatMulVec DeltaR2 yhat
  let vR2 : Fin m -> Real := rectMatMulVec R2 yhat
  let v1 : Fin m -> Real :=
    rectMatMulVec (finiteTranspose DeltaR1) vR2
  let lifted : Fin m -> Real := rectMatMulVec (finiteTranspose Rinv) v1
  have hD1 : frobNorm DeltaR1 <= theta * frobNorm R :=
    frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      DeltaR1 R htheta hDeltaR1
  have hD2 : frobNorm DeltaR2 <= theta * frobNorm R :=
    frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      DeltaR2 R htheta hDeltaR2
  have hR2 : frobNorm R2 <= frobNorm R + theta * frobNorm R := by
    calc
      frobNorm R2 <= frobNorm R + frobNorm DeltaR2 := by
        simpa [R2] using frobNorm_add_le R DeltaR2
      _ <= frobNorm R + theta * frobNorm R := add_le_add le_rfl hD2
  have hR2radius : frobNorm R2 <=
      frobNorm R + radius * frobNorm R := by
    exact hR2.trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right htheta_radius (frobNorm_nonneg R)))
  have hv2 : vecNorm2 v2 <= theta * frobNorm R * vecNorm2 yhat := by
    calc
      vecNorm2 v2 <= frobNormRect DeltaR2 * vecNorm2 yhat := by
        simpa [v2] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul DeltaR2 yhat
      _ = frobNorm DeltaR2 * vecNorm2 yhat := by
        rw [frobNormRect_eq_frobNorm]
      _ <= (theta * frobNorm R) * vecNorm2 yhat :=
        mul_le_mul_of_nonneg_right hD2 (vecNorm2_nonneg _)
      _ = theta * frobNorm R * vecNorm2 yhat := rfl
  have hvR2 : vecNorm2 vR2 <=
      (frobNorm R + radius * frobNorm R) * vecNorm2 yhat := by
    calc
      vecNorm2 vR2 <= frobNormRect R2 * vecNorm2 yhat := by
        simpa [vR2] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul R2 yhat
      _ = frobNorm R2 * vecNorm2 yhat := by
        rw [frobNormRect_eq_frobNorm]
      _ <= (frobNorm R + radius * frobNorm R) * vecNorm2 yhat :=
        mul_le_mul_of_nonneg_right hR2radius (vecNorm2_nonneg _)
  have hv1 : vecNorm2 v1 <=
      (theta * frobNorm R) *
        ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat) := by
    have hbase : vecNorm2 v1 <= frobNorm DeltaR1 * vecNorm2 vR2 := by
      calc
        vecNorm2 v1 <= frobNormRect (finiteTranspose DeltaR1) *
            vecNorm2 vR2 := by
          simpa [v1] using
            vecNorm2_rectMatMulVec_le_frobNormRect_mul
              (finiteTranspose DeltaR1) vR2
        _ = frobNorm DeltaR1 * vecNorm2 vR2 := by
          rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNorm]
    calc
      vecNorm2 v1 <= frobNorm DeltaR1 * vecNorm2 vR2 := hbase
      _ <= (theta * frobNorm R) * vecNorm2 vR2 :=
        mul_le_mul_of_nonneg_right hD1 (vecNorm2_nonneg _)
      _ <= (theta * frobNorm R) *
          ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat) :=
        mul_le_mul_of_nonneg_left hvR2
          (mul_nonneg htheta (frobNorm_nonneg R))
  have hlifted : vecNorm2 lifted <=
      frobNorm Rinv *
        ((theta * frobNorm R) *
          ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat)) := by
    calc
      vecNorm2 lifted <= frobNormRect (finiteTranspose Rinv) *
          vecNorm2 v1 := by
        simpa [lifted] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul
            (finiteTranspose Rinv) v1
      _ = frobNorm Rinv * vecNorm2 v1 := by
        rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNorm]
      _ <= frobNorm Rinv *
          ((theta * frobNorm R) *
            ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat)) :=
        mul_le_mul_of_nonneg_left hv1 (frobNorm_nonneg _)
  have hraw := higham21_dh1993_factor_difference_raw
    R Rinv DeltaR1 DeltaR2 ybar yhat hInv hNormal
  have hRd : rectMatMulVec R d = fun i => v2 i + lifted i := by
    simpa [d, v2, lifted, v1, vR2, R2] using hraw
  have hd : d = rectMatMulVec Rinv (fun i => v2 i + lifted i) := by
    rw [← hRd]
    exact (rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 d).symm
  have hsum : vecNorm2 (fun i => v2 i + lifted i) <=
      theta * frobNorm R * vecNorm2 yhat +
        frobNorm Rinv *
          ((theta * frobNorm R) *
            ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat)) := by
    exact (vecNorm2_add_le v2 lifted).trans (add_le_add hv2 hlifted)
  calc
    vecNorm2 (fun i => ybar i - yhat i) = vecNorm2 d := by rfl
    _ = vecNorm2 (rectMatMulVec Rinv (fun i => v2 i + lifted i)) := by rw [hd]
    _ <= frobNormRect Rinv * vecNorm2 (fun i => v2 i + lifted i) :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul Rinv _
    _ = frobNorm Rinv * vecNorm2 (fun i => v2 i + lifted i) := by
      rw [frobNormRect_eq_frobNorm]
    _ <= frobNorm Rinv *
        (theta * frobNorm R * vecNorm2 yhat +
          frobNorm Rinv *
            ((theta * frobNorm R) *
              ((frobNorm R + radius * frobNorm R) * vecNorm2 yhat))) :=
      mul_le_mul_of_nonneg_left hsum (frobNorm_nonneg _)
    _ = theta *
        (frobNorm Rinv *
          (frobNorm R +
            frobNorm Rinv * frobNorm R *
              (frobNorm R + radius * frobNorm R)) *
          vecNorm2 yhat) := by ring

/-- The explicit signed higher-order expression is uniformly quadratic once
the QR perturbation has a first-order Frobenius bound and the two triangular
solve perturbations share a fixed radius.

The coefficient is deliberately expanded in primitive norms. It contains no
division by `theta` and is therefore suitable for a genuine fixed-radius
`O(theta²)` argument. -/
theorem higham21_dh1993_signed_remainder_vecNorm2_le_radius
    {m n : Nat}
    (theta radius KF : Real)
    (htheta : 0 <= theta) (htheta_radius : theta <= radius)
    (hKF : 0 <= KF)
    (F : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat : Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hInv : IsInverse m R Rinv)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat))
    (hDeltaR1 : forall i j, |DeltaR1 i j| <= theta * |R i j|)
    (hDeltaR2 : forall i j, |DeltaR2 i j| <= theta * |R i j|)
    (hF : frobNorm F <= theta * KF) :
    let Kd :=
      frobNorm Rinv *
        (frobNorm R +
          frobNorm Rinv * frobNorm R *
            (frobNorm R + radius * frobNorm R)) *
        vecNorm2 yhat
    vecNorm2
        (higham21SNEDHSignedRemainderAt
          F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
      theta ^ 2 *
        (frobNorm R * Kd +
          frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
          KF * Kd) := by
  dsimp only
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let Kd : Real :=
    frobNorm Rinv *
      (frobNorm R +
        frobNorm Rinv * frobNorm R *
          (frobNorm R + radius * frobNorm R)) *
      vecNorm2 yhat
  let a : Fin m -> Real :=
    rectMatMulVec DeltaR2 (fun k => yhat k - ybar k)
  let q : Fin m -> Real := fun k =>
    rectMatMulVec DeltaR2 yhat k - rectMatMulVec R d k
  let b1 : Fin m -> Real := rectMatMulVec (finiteTranspose DeltaR1) q
  let b2 : Fin m -> Real := rectMatMulVec (finiteTranspose Rinv) b1
  let factorRem : Fin m -> Real := fun i => a i + b2 i
  let fRem : Fin n -> Real := rectTransposeMulVec F d
  have hD1 : frobNorm DeltaR1 <= theta * frobNorm R :=
    frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      DeltaR1 R htheta hDeltaR1
  have hD2 : frobNorm DeltaR2 <= theta * frobNorm R :=
    frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      DeltaR2 R htheta hDeltaR2
  have hd : vecNorm2 d <= theta * Kd := by
    simpa [d, Kd] using
      higham21_dh1993_factor_difference_vecNorm2_le_radius
        theta radius htheta htheta_radius R Rinv DeltaR1 DeltaR2
          ybar yhat hInv hNormal hDeltaR1 hDeltaR2
  have ha : vecNorm2 a <= theta ^ 2 * (frobNorm R * Kd) := by
    have hdiffNorm : vecNorm2 (fun k => yhat k - ybar k) = vecNorm2 d := by
      have hneg : (fun k => yhat k - ybar k) = fun k => -d k := by
        ext k
        simp [d]
      rw [hneg, vecNorm2_neg]
    have hbase : vecNorm2 a <= frobNorm DeltaR2 * vecNorm2 d := by
      calc
        vecNorm2 a <= frobNormRect DeltaR2 * vecNorm2 d := by
          rw [← hdiffNorm]
          simpa [a] using
            vecNorm2_rectMatMulVec_le_frobNormRect_mul DeltaR2
              (fun k => yhat k - ybar k)
        _ = frobNorm DeltaR2 * vecNorm2 d := by
          rw [frobNormRect_eq_frobNorm]
    calc
      vecNorm2 a <= frobNorm DeltaR2 * vecNorm2 d := hbase
      _ <= (theta * frobNorm R) * (theta * Kd) :=
        mul_le_mul hD2 hd (vecNorm2_nonneg _) (by
          exact mul_nonneg htheta (frobNorm_nonneg R))
      _ = theta ^ 2 * (frobNorm R * Kd) := by ring
  have hD2y : vecNorm2 (rectMatMulVec DeltaR2 yhat) <=
      theta * frobNorm R * vecNorm2 yhat := by
    calc
      vecNorm2 (rectMatMulVec DeltaR2 yhat) <=
          frobNormRect DeltaR2 * vecNorm2 yhat :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul DeltaR2 yhat
      _ = frobNorm DeltaR2 * vecNorm2 yhat := by
        rw [frobNormRect_eq_frobNorm]
      _ <= (theta * frobNorm R) * vecNorm2 yhat :=
        mul_le_mul_of_nonneg_right hD2 (vecNorm2_nonneg _)
      _ = theta * frobNorm R * vecNorm2 yhat := rfl
  have hRd : vecNorm2 (rectMatMulVec R d) <=
      frobNorm R * (theta * Kd) := by
    calc
      vecNorm2 (rectMatMulVec R d) <= frobNormRect R * vecNorm2 d :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul R d
      _ = frobNorm R * vecNorm2 d := by rw [frobNormRect_eq_frobNorm]
      _ <= frobNorm R * (theta * Kd) :=
        mul_le_mul_of_nonneg_left hd (frobNorm_nonneg _)
  have hq : vecNorm2 q <=
      theta * frobNorm R * (vecNorm2 yhat + Kd) := by
    have hsub :
        vecNorm2
            (fun k => rectMatMulVec DeltaR2 yhat k - rectMatMulVec R d k) <=
          vecNorm2 (rectMatMulVec DeltaR2 yhat) +
            vecNorm2 (rectMatMulVec R d) := by
      simpa [sub_eq_add_neg, vecNorm2_neg] using
        vecNorm2_add_le (rectMatMulVec DeltaR2 yhat)
          (fun k => -rectMatMulVec R d k)
    calc
      vecNorm2 q <= vecNorm2 (rectMatMulVec DeltaR2 yhat) +
          vecNorm2 (rectMatMulVec R d) := by
        simpa [q] using hsub
      _ <= theta * frobNorm R * vecNorm2 yhat +
          frobNorm R * (theta * Kd) := add_le_add hD2y hRd
      _ = theta * frobNorm R * (vecNorm2 yhat + Kd) := by ring
  have hb1 : vecNorm2 b1 <=
      (theta * frobNorm R) *
        (theta * frobNorm R * (vecNorm2 yhat + Kd)) := by
    have hbase : vecNorm2 b1 <= frobNorm DeltaR1 * vecNorm2 q := by
      calc
        vecNorm2 b1 <= frobNormRect (finiteTranspose DeltaR1) *
            vecNorm2 q := by
          simpa [b1] using
            vecNorm2_rectMatMulVec_le_frobNormRect_mul
              (finiteTranspose DeltaR1) q
        _ = frobNorm DeltaR1 * vecNorm2 q := by
          rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNorm]
    calc
      vecNorm2 b1 <= frobNorm DeltaR1 * vecNorm2 q := hbase
      _ <= (theta * frobNorm R) * vecNorm2 q :=
        mul_le_mul_of_nonneg_right hD1 (vecNorm2_nonneg _)
      _ <= (theta * frobNorm R) *
          (theta * frobNorm R * (vecNorm2 yhat + Kd)) :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg htheta (frobNorm_nonneg R))
  have hb2 : vecNorm2 b2 <= theta ^ 2 *
      (frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) := by
    calc
      vecNorm2 b2 <= frobNormRect (finiteTranspose Rinv) * vecNorm2 b1 := by
        simpa [b2] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul
            (finiteTranspose Rinv) b1
      _ = frobNorm Rinv * vecNorm2 b1 := by
        rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNorm]
      _ <= frobNorm Rinv *
          ((theta * frobNorm R) *
            (theta * frobNorm R * (vecNorm2 yhat + Kd))) :=
        mul_le_mul_of_nonneg_left hb1 (frobNorm_nonneg _)
      _ = theta ^ 2 *
          (frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) := by
        ring
  have hfactor : vecNorm2 factorRem <= theta ^ 2 *
      (frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) := by
    calc
      vecNorm2 factorRem <= vecNorm2 a + vecNorm2 b2 := by
        simpa [factorRem] using vecNorm2_add_le a b2
      _ <= theta ^ 2 * (frobNorm R * Kd) +
          theta ^ 2 *
            (frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) :=
        add_le_add ha hb2
      _ = theta ^ 2 *
          (frobNorm R * Kd +
            frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) := by
        ring
  have hfRem : vecNorm2 fRem <= theta ^ 2 * (KF * Kd) := by
    have hbase : vecNorm2 fRem <= frobNorm F * vecNorm2 d := by
      calc
        vecNorm2 fRem <= frobNormRect (finiteTranspose F) * vecNorm2 d := by
          simpa [fRem, rectTransposeMulVec] using
            vecNorm2_rectMatMulVec_le_frobNormRect_mul (finiteTranspose F) d
        _ = frobNorm F * vecNorm2 d := by
          rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNormFn]
    calc
      vecNorm2 fRem <= frobNorm F * vecNorm2 d := hbase
      _ <= (theta * KF) * (theta * Kd) :=
        mul_le_mul hF hd (vecNorm2_nonneg _) (mul_nonneg htheta hKF)
      _ = theta ^ 2 * (KF * Kd) := by ring
  have hQrem : vecNorm2 (rectMatMulVec Q factorRem) <=
      vecNorm2 factorRem := by
    simpa using hQ.rectOpNorm2Le_one factorRem
  have hshape :
      higham21SNEDHSignedRemainderAt
          F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar =
        fun j => -rectMatMulVec Q factorRem j + fRem j := by
    rfl
  rw [hshape]
  calc
    vecNorm2 (fun j => -rectMatMulVec Q factorRem j + fRem j) <=
        vecNorm2 (rectMatMulVec Q factorRem) + vecNorm2 fRem := by
      simpa [vecNorm2_neg] using
        vecNorm2_add_le (fun j => -rectMatMulVec Q factorRem j) fRem
    _ <= vecNorm2 factorRem + vecNorm2 fRem := add_le_add hQrem le_rfl
    _ <= theta ^ 2 *
          (frobNorm R * Kd +
            frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd)) +
        theta ^ 2 * (KF * Kd) := add_le_add hfactor hfRem
    _ = theta ^ 2 *
        (frobNorm R * Kd +
          frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
          KF * Kd) := by ring





























































































































































/-- The source absolute transpose action at a perturbed dual vector is
controlled directly by the original row-scaled condition number.  The only
extra term is the Frobenius action on the dual-vector displacement. -/
theorem higham21_sne_source_abs_action_le_cond2_plus_change
    {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (x : Fin n -> Real) (y ybar : Fin m -> Real)
    (hy : y = rectTransposeMulVec Aplus x) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      higham21Cond2With A Aplus * vecNorm2 x +
        frobNorm A * vecNorm2 (fun i => ybar i - y i) := by
  have hchange := higham21_sne_source_abs_action_change A y ybar
  have hdual := higham21_sne_dual_majorant_le_cond2 A Aplus x
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) +
        frobNorm A * vecNorm2 (fun i => y i - ybar i) := hchange
    _ <= higham21Cond2With A Aplus * vecNorm2 x +
        frobNorm A * vecNorm2 (fun i => y i - ybar i) :=
      add_le_add (by simpa [hy] using hdual) le_rfl
    _ = higham21Cond2With A Aplus * vecNorm2 x +
        frobNorm A * vecNorm2 (fun i => ybar i - y i) := by
      rw [vecNorm2_sub_comm]

/-- Radius form of `higham21_sne_source_abs_action_le_cond2_plus_change`.
The coefficient contains no division by the active radius. -/
theorem higham21_sne_source_abs_action_le_cond2_plus_radius_change
    {m n : Nat}
    (theta Ky : Real) (_htheta : 0 <= theta) (_hKy : 0 <= Ky)
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (x : Fin n -> Real) (y ybar : Fin m -> Real)
    (hy : y = rectTransposeMulVec Aplus x)
    (hchange : vecNorm2 (fun i => ybar i - y i) <= theta * Ky) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      higham21Cond2With A Aplus * vecNorm2 x +
        theta * (frobNorm A * Ky) := by
  have hsource :=
    higham21_sne_source_abs_action_le_cond2_plus_change
      A Aplus x y ybar hy
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      higham21Cond2With A Aplus * vecNorm2 x +
        frobNorm A * vecNorm2 (fun i => ybar i - y i) := hsource
    _ <= higham21Cond2With A Aplus * vecNorm2 x +
        frobNorm A * (theta * Ky) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hchange (frobNorm_nonneg A))
    _ = higham21Cond2With A Aplus * vecNorm2 x +
        theta * (frobNorm A * Ky) := by ring

/-- A componentwise Householder QR action has the original source condition
term at first order.  Moving the nearby dual vector back to the exact one is
quadratic when both radii are bounded by `theta`. -/
theorem higham21_sne_qr_action_le_source_cond2_plus_quadratic
    {m n : Nat}
    (theta rho Ky : Real)
    (htheta : 0 <= theta) (hrho : 0 <= rho) (hrho_theta : rho <= theta)
    (hKy : 0 <= Ky)
    (A F : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (x : Fin n -> Real) (y ybar : Fin m -> Real)
    (hy : y = rectTransposeMulVec Aplus x)
    (hybar : vecNorm2 (fun i => ybar i - y i) <= theta * Ky)
    (hQR : vecNorm2 (rectTransposeMulVec F ybar) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|))) :
    vecNorm2 (rectTransposeMulVec F ybar) <=
      rho * higham21Cond2With A Aplus * vecNorm2 x +
        theta ^ 2 * (frobNorm A * Ky) := by
  have hsource :=
    higham21_sne_source_abs_action_le_cond2_plus_radius_change
      theta Ky htheta hKy A Aplus x y ybar hy hybar
  have hrhotheta : rho * theta <= theta ^ 2 := by
    nlinarith
  calc
    vecNorm2 (rectTransposeMulVec F ybar) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) := hQR
    _ <= rho *
        (higham21Cond2With A Aplus * vecNorm2 x +
          theta * (frobNorm A * Ky)) :=
      mul_le_mul_of_nonneg_left hsource hrho
    _ = rho * higham21Cond2With A Aplus * vecNorm2 x +
        (rho * theta) * (frobNorm A * Ky) := by ring
    _ <= rho * higham21Cond2With A Aplus * vecNorm2 x +
        theta ^ 2 * (frobNorm A * Ky) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hrhotheta
          (mul_nonneg (frobNorm_nonneg A) hKy))

/-- The actual rounded final formation has the source condition term at first
order.  Displacing first to the QR reference and then to the rounded normal
solution contributes only a radius-squared term. -/
theorem higham21_sne_formation_le_source_cond2_plus_quadratic
    {m n : Nat}
    (theta gamma Ky Kd : Real)
    (htheta : 0 <= theta) (hgamma : 0 <= gamma)
    (hgamma_theta : gamma <= theta)
    (hKy : 0 <= Ky) (hKd : 0 <= Kd)
    (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (x : Fin n -> Real) (y ybar yhat : Fin m -> Real)
    (g : Fin n -> Real)
    (hy : y = rectTransposeMulVec Aplus x)
    (hybar : vecNorm2 (fun i => ybar i - y i) <= theta * Ky)
    (hyhat : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd)
    (hFormation : vecNorm2 g <= gamma *
      vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|))) :
    vecNorm2 g <=
      gamma * higham21Cond2With A Aplus * vecNorm2 x +
        theta ^ 2 * (frobNorm A * (Ky + Kd)) := by
  have hbar :=
    higham21_sne_source_abs_action_le_cond2_plus_radius_change
      theta Ky htheta hKy A Aplus x y ybar hy hybar
  have hmove := higham21_sne_source_abs_action_change A ybar yhat
  have hsource :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        higham21Cond2With A Aplus * vecNorm2 x +
          theta * (frobNorm A * (Ky + Kd)) := by
    calc
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
          frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := hmove
      _ <= (higham21Cond2With A Aplus * vecNorm2 x +
          theta * (frobNorm A * Ky)) + frobNorm A * (theta * Kd) :=
        add_le_add hbar
          (mul_le_mul_of_nonneg_left hyhat (frobNorm_nonneg A))
      _ = higham21Cond2With A Aplus * vecNorm2 x +
          theta * (frobNorm A * (Ky + Kd)) := by ring
  have hgammatheta : gamma * theta <= theta ^ 2 := by
    nlinarith
  calc
    vecNorm2 g <= gamma *
      vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) :=
      hFormation
    _ <= gamma *
        (higham21Cond2With A Aplus * vecNorm2 x +
          theta * (frobNorm A * (Ky + Kd))) :=
      mul_le_mul_of_nonneg_left hsource hgamma
    _ = gamma * higham21Cond2With A Aplus * vecNorm2 x +
        (gamma * theta) * (frobNorm A * (Ky + Kd)) := by ring
    _ <= gamma * higham21Cond2With A Aplus * vecNorm2 x +
        theta ^ 2 * (frobNorm A * (Ky + Kd)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hgammatheta
          (mul_nonneg (frobNorm_nonneg A) (add_nonneg hKy hKd)))





































































































































end NumStability
