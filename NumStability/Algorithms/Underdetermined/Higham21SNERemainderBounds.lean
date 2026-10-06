-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Uniform local bounds for the signed SNE higher-order terms.

import NumStability.Algorithms.Underdetermined.Higham21SNEQRMajorant

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

/-- Moving the vector in an absolute transpose action costs at most the
Frobenius norm of the matrix times the vector displacement. -/
theorem higham21_sne_source_abs_action_change
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
  let wbar : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wd : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A)
      (fun i => |ybar i - yhat i|)
  let what : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)
  have hwbar : forall j, 0 <= wbar j := by
    intro j
    dsimp [wbar, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwd : forall j, 0 <= wd j := by
    intro j
    dsimp [wd, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwhat : forall j, 0 <= what j := by
    intro j
    dsimp [what, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpoint : forall j, |what j| <= wbar j + wd j := by
    intro j
    rw [abs_of_nonneg (hwhat j)]
    dsimp [what, wbar, wd, rectTransposeMulVec, absMatrixRect]
    calc
      ∑ i : Fin m, |A i j| * |yhat i| <=
          ∑ i : Fin m, |A i j| * (|ybar i| + |ybar i - yhat i|) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |yhat i| <= |ybar i| + |ybar i - yhat i| := by
          calc
            |yhat i| = |ybar i - (ybar i - yhat i)| := by
              congr 1
              ring
            _ <= |ybar i| + |ybar i - yhat i| := abs_sub _ _
        exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      _ = (∑ i : Fin m, |A i j| * |ybar i|) +
          ∑ i : Fin m, |A i j| * |ybar i - yhat i| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmajor : vecNorm2 what <= vecNorm2 (fun j => wbar j + wd j) := by
    apply vecNorm2_le_of_abs_le
    intro j
    simpa [abs_of_nonneg (add_nonneg (hwbar j) (hwd j))] using hpoint j
  have hwdNorm : vecNorm2 wd <=
      frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
    calc
      vecNorm2 wd <= frobNormRect (finiteTranspose (absMatrixRect A)) *
          vecNorm2 (fun i => |ybar i - yhat i|) := by
        simpa [wd, rectTransposeMulVec] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul
            (finiteTranspose (absMatrixRect A))
            (fun i => |ybar i - yhat i|)
      _ = frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
        rw [frobNormRect_finiteTranspose]
        rw [show frobNormRect (absMatrixRect A) = frobNormRect A by
          simpa [absMatrixRect] using frobNormRect_abs A]
        rw [frobNormRect_eq_frobNormFn]
        rw [show vecNorm2 (fun i => |ybar i - yhat i|) =
            vecNorm2 (fun i => ybar i - yhat i) by
          simpa using vecNorm2_abs (fun i => ybar i - yhat i)]
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) =
        vecNorm2 what := by rfl
    _ <= vecNorm2 (fun j => wbar j + wd j) := hmajor
    _ <= vecNorm2 wbar + vecNorm2 wd := vecNorm2_add_le wbar wd
    _ <= vecNorm2 wbar +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) :=
      add_le_add le_rfl hwdNorm
    _ = vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by rfl

/-- Source-shaped leading/quadratic split for the final rounded `Aᵀ yhat`
formation.  The nearby dual action supplies the leading term; applying the
formation to `yhat-ybar` is quadratic. -/
theorem higham21_sne_formation_error_le_source_plus_quadratic
    {m n : Nat}
    (theta rho gamma Kd q : Real)
    (htheta : 0 <= theta)
    (_hrho : 0 <= rho) (hrho_theta : rho <= theta) (hrho_lt : rho < 1)
    (hgamma : 0 <= gamma) (hgamma_theta : gamma <= theta)
    (hKd : 0 <= Kd) (hq : 0 <= q)
    (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) (g : Fin n -> Real)
    (hFormation :
      vecNorm2 g <= gamma *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)))
    (hbar :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
        q / (1 - rho))
    (hd : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd) :
    vecNorm2 g <=
      theta * q + theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hqdiv : 0 <= q / (1 - rho) := div_nonneg hq hden.le
  have hA : 0 <= frobNorm A := frobNorm_nonneg A
  have hsource := higham21_sne_source_abs_action_change A ybar yhat
  have hhat :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        q / (1 - rho) + frobNorm A * (theta * Kd) := by
    exact hsource.trans (add_le_add hbar
      (mul_le_mul_of_nonneg_left hd hA))
  have hgammaBound : vecNorm2 g <=
      theta * (q / (1 - rho) + frobNorm A * (theta * Kd)) := by
    calc
      vecNorm2 g <= gamma *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) :=
        hFormation
      _ <= gamma *
          (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
        mul_le_mul_of_nonneg_left hhat hgamma
      _ <= theta *
          (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
        mul_le_mul_of_nonneg_right hgamma_theta
          (add_nonneg hqdiv (mul_nonneg hA (mul_nonneg htheta hKd)))
  have hsplit : theta * (q / (1 - rho)) <=
      theta * q + theta ^ 2 * (q / (1 - rho)) := by
    have hidentity : q / (1 - rho) = q + rho * (q / (1 - rho)) := by
      field_simp [ne_of_gt hden]
      ring
    calc
      theta * (q / (1 - rho)) =
          theta * (q + rho * (q / (1 - rho))) :=
        congrArg (fun z => theta * z) hidentity
      _ =
          theta * q + theta * rho * (q / (1 - rho)) := by ring
      _ <= theta * q + theta * theta * (q / (1 - rho)) := by
        gcongr
      _ = theta * q + theta ^ 2 * (q / (1 - rho)) := by ring
  calc
    vecNorm2 g <=
        theta * (q / (1 - rho) + frobNorm A * (theta * Kd)) := hgammaBound
    _ = theta * (q / (1 - rho)) +
        theta ^ 2 * (frobNorm A * Kd) := by ring
    _ <= (theta * q + theta ^ 2 * (q / (1 - rho))) +
        theta ^ 2 * (frobNorm A * Kd) := add_le_add hsplit le_rfl
    _ = theta * q + theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
      ring

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

/-- The explicit finite remainder in equation (21.11) is uniformly quadratic
once the matrix perturbation, dual displacement, and forward displacement are
each first order.  The coefficient is expanded in primitive Frobenius norms
and contains no division by the active radius. -/
theorem higham21_eq21_11_finite_remainder_vecNorm2_le_radius
    {m n : Nat}
    (eta KF Ky Kx : Real)
    (heta : 0 <= eta) (hKF : 0 <= KF) (_hKy : 0 <= Ky) (_hKx : 0 <= Kx)
    (A F : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (xhat : Fin n -> Real) (yhat : Fin m -> Real)
    (hF : frobNorm F <= eta * KF)
    (hy :
      let Aplus := undetAplusOfGramNonsingInv A
      let x := rectMatMulVec Aplus b
      let y := rectTransposeMulVec Aplus x
      vecNorm2 (fun i => yhat i - y i) <= eta * Ky)
    (hx :
      let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
      vecNorm2 (fun j => xhat j - x j) <= eta * Kx) :
    vecNorm2 (higham21Eq21_11FiniteRemainder A F b xhat yhat) <=
      eta ^ 2 *
        (KF *
          ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * Ky +
            frobNorm (undetAplusOfGramNonsingInv A) * Kx)) := by
  dsimp only at hy hx
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let y : Fin m -> Real := rectTransposeMulVec Aplus x
  let dy : Fin m -> Real := fun i => yhat i - y i
  let dx : Fin n -> Real := fun j => xhat j - x j
  let dualTerm : Fin n -> Real := rectTransposeMulVec F dy
  let projected : Fin n -> Real :=
    rectMatMulVec Aplus (rectMatMulVec A dualTerm)
  let forwardTerm : Fin n -> Real :=
    rectMatMulVec Aplus (rectMatMulVec F dx)
  have hdy : vecNorm2 dy <= eta * Ky := by simpa [dy, y, x, Aplus] using hy
  have hdx : vecNorm2 dx <= eta * Kx := by simpa [dx, x, Aplus] using hx
  have hdualTerm : vecNorm2 dualTerm <= eta ^ 2 * (KF * Ky) := by
    calc
      vecNorm2 dualTerm <=
          frobNormRect (finiteTranspose F) * vecNorm2 dy := by
        simpa [dualTerm, rectTransposeMulVec] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul (finiteTranspose F) dy
      _ = frobNorm F * vecNorm2 dy := by
        rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNormFn]
      _ <= (eta * KF) * (eta * Ky) :=
        mul_le_mul hF hdy (vecNorm2_nonneg _)
          (mul_nonneg heta hKF)
      _ = eta ^ 2 * (KF * Ky) := by ring
  have hprojected : vecNorm2 projected <=
      eta ^ 2 *
        (frobNorm Aplus * frobNorm A * (KF * Ky)) := by
    calc
      vecNorm2 projected <=
          frobNormRect Aplus * vecNorm2 (rectMatMulVec A dualTerm) := by
        simpa [projected] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul Aplus
            (rectMatMulVec A dualTerm)
      _ = frobNorm Aplus * vecNorm2 (rectMatMulVec A dualTerm) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus * (frobNormRect A * vecNorm2 dualTerm) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_rectMatMulVec_le_frobNormRect_mul A dualTerm)
          (frobNorm_nonneg Aplus)
      _ = frobNorm Aplus * (frobNorm A * vecNorm2 dualTerm) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus *
          (frobNorm A * (eta ^ 2 * (KF * Ky))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdualTerm (frobNorm_nonneg A))
          (frobNorm_nonneg Aplus)
      _ = eta ^ 2 *
          (frobNorm Aplus * frobNorm A * (KF * Ky)) := by ring
  have hFdx : vecNorm2 (rectMatMulVec F dx) <=
      eta ^ 2 * (KF * Kx) := by
    calc
      vecNorm2 (rectMatMulVec F dx) <= frobNormRect F * vecNorm2 dx :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul F dx
      _ = frobNorm F * vecNorm2 dx := by rw [frobNormRect_eq_frobNormFn]
      _ <= (eta * KF) * (eta * Kx) :=
        mul_le_mul hF hdx (vecNorm2_nonneg _)
          (mul_nonneg heta hKF)
      _ = eta ^ 2 * (KF * Kx) := by ring
  have hforwardTerm : vecNorm2 forwardTerm <=
      eta ^ 2 * (frobNorm Aplus * (KF * Kx)) := by
    calc
      vecNorm2 forwardTerm <=
          frobNormRect Aplus * vecNorm2 (rectMatMulVec F dx) := by
        simpa [forwardTerm] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul Aplus
            (rectMatMulVec F dx)
      _ = frobNorm Aplus * vecNorm2 (rectMatMulVec F dx) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus * (eta ^ 2 * (KF * Kx)) :=
        mul_le_mul_of_nonneg_left hFdx (frobNorm_nonneg Aplus)
      _ = eta ^ 2 * (frobNorm Aplus * (KF * Kx)) := by ring
  have hshape :
      higham21Eq21_11FiniteRemainder A F b xhat yhat =
        fun j => (dualTerm j - projected j) - forwardTerm j := by
    rfl
  have htri1 : vecNorm2 (fun j => dualTerm j - projected j) <=
      vecNorm2 dualTerm + vecNorm2 projected := by
    simpa [sub_eq_add_neg, vecNorm2_neg] using
      vecNorm2_add_le dualTerm (fun j => -projected j)
  have htri2 :
      vecNorm2 (fun j => (dualTerm j - projected j) - forwardTerm j) <=
        vecNorm2 (fun j => dualTerm j - projected j) +
          vecNorm2 forwardTerm := by
    simpa [sub_eq_add_neg, vecNorm2_neg] using
      vecNorm2_add_le (fun j => dualTerm j - projected j)
        (fun j => -forwardTerm j)
  rw [hshape]
  calc
    vecNorm2 (fun j => (dualTerm j - projected j) - forwardTerm j) <=
        vecNorm2 (fun j => dualTerm j - projected j) +
          vecNorm2 forwardTerm := htri2
    _ <= (vecNorm2 dualTerm + vecNorm2 projected) +
          vecNorm2 forwardTerm := add_le_add htri1 le_rfl
    _ <= (eta ^ 2 * (KF * Ky) +
          eta ^ 2 * (frobNorm Aplus * frobNorm A * (KF * Ky))) +
          eta ^ 2 * (frobNorm Aplus * (KF * Kx)) :=
      add_le_add (add_le_add hdualTerm hprojected) hforwardTerm
    _ = eta ^ 2 *
        (KF *
          ((1 + frobNorm Aplus * frobNorm A) * Ky +
            frobNorm Aplus * Kx)) := by ring
    _ = eta ^ 2 *
        (KF *
          ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * Ky +
            frobNorm (undetAplusOfGramNonsingInv A) * Kx)) := by
      rfl

end NumStability
