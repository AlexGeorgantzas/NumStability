-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Signed factorwise algebra for the seminormal-equations analysis.

import NumStability.Algorithms.Underdetermined.Higham21SNEActualOutput

namespace NumStability

open scoped BigOperators

/-!
# Signed SNE factorwise identities

This module retains the two triangular-solve perturbations separately.  Its
core identities are the exact finite counterparts of Demmel--Higham (1993),
equations (3.10)--(3.17); no asymptotic `O(u^2)` term is discarded.
-/

/-- Leading factor-difference term, with a selectable second-factor pivot.

Taking `z = yhat` gives the literal first-order expression used before
Demmel--Higham (3.17).  Taking `z = ybar` moves the additional product
`DeltaR2 * (yhat - ybar)` into the finite remainder. -/
noncomputable def higham21SNEDHFactorLeadingAt {m : Nat}
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar z : Fin m -> Real) : Fin m -> Real :=
  fun i =>
    rectMatMulVec (finiteTranspose Rinv)
        (rectMatMulVec (finiteTranspose DeltaR1)
          (rectMatMulVec R ybar)) i +
      rectMatMulVec DeltaR2 z i

/-- Exact finite remainder associated with
`higham21SNEDHFactorLeadingAt`. -/
noncomputable def higham21SNEDHFactorRemainderAt {m : Nat}
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat z : Fin m -> Real) : Fin m -> Real :=
  let d : Fin m -> Real := fun i => ybar i - yhat i
  fun i =>
    rectMatMulVec DeltaR2 (fun k => yhat k - z k) i +
      rectMatMulVec (finiteTranspose Rinv)
        (rectMatMulVec (finiteTranspose DeltaR1)
          (fun k =>
            rectMatMulVec DeltaR2 yhat k -
              rectMatMulVec R d k)) i

/-- Exact uncollected consequence of the two perturbed triangular factors:

`R (ybar-yhat) = DeltaR2*yhat
  + R^{-T} DeltaR1^T (R+DeltaR2)*yhat`.

This is the finite identity behind the first displayed manipulation preceding
Demmel--Higham (3.17). -/
theorem higham21_dh1993_factor_difference_raw
    {m : Nat}
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat : Fin m -> Real)
    (hInv : IsInverse m R Rinv)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat)) :
    rectMatMulVec R (fun i => ybar i - yhat i) =
      fun i =>
        rectMatMulVec DeltaR2 yhat i +
          rectMatMulVec (finiteTranspose Rinv)
            (rectMatMulVec (finiteTranspose DeltaR1)
              (rectMatMulVec
                (fun i j => R i j + DeltaR2 i j) yhat)) i := by
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let v : Fin m -> Real :=
    rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat
  have hNormal' :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        fun i =>
          rectMatMulVec (finiteTranspose R) v i +
            rectMatMulVec (finiteTranspose DeltaR1) v i := by
    rw [show
      finiteTranspose (fun i j => R i j + DeltaR1 i j) =
        (fun i j => finiteTranspose R i j + finiteTranspose DeltaR1 i j) by
          rfl] at hNormal
    rw [rectMatMulVec_mat_add] at hNormal
    simpa [v] using hNormal
  have hv :
      v = fun i =>
        rectMatMulVec R yhat i + rectMatMulVec DeltaR2 yhat i := by
    simpa [v] using rectMatMulVec_mat_add R DeltaR2 yhat
  have hRd :
      rectMatMulVec R d =
        fun i => rectMatMulVec R ybar i - rectMatMulVec R yhat i := by
    simpa [d] using rectMatMulVec_sub R ybar yhat
  have hRTv :
      rectMatMulVec (finiteTranspose R) v =
        fun i =>
          rectMatMulVec (finiteTranspose R) (rectMatMulVec R yhat) i +
            rectMatMulVec (finiteTranspose R)
              (rectMatMulVec DeltaR2 yhat) i := by
    rw [hv, rectMatMulVec_add]
  have hRT :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R d) =
        fun i =>
          rectMatMulVec (finiteTranspose R)
              (rectMatMulVec DeltaR2 yhat) i +
            rectMatMulVec (finiteTranspose DeltaR1) v i := by
    rw [hRd, rectMatMulVec_sub]
    ext i
    have hi := congrFun hNormal' i
    rw [congrFun hRTv i] at hi
    linarith
  have hApplied := congrArg (rectMatMulVec (finiteTranspose Rinv)) hRT
  rw [rectMatMulVec_add] at hApplied
  have hTInv := isInverse_finiteTranspose hInv
  rw [rectMatMulVec_left_inverse_of_IsLeftInverse hTInv.1] at hApplied
  rw [rectMatMulVec_left_inverse_of_IsLeftInverse hTInv.1] at hApplied
  simpa [d, v] using hApplied

/-- Pivoted exact factor-difference identity.

For `z = yhat` the second term of the leading expression is exactly
`DeltaR2*yhat`, as in the source derivation of (3.17).  For `z = ybar`, every
term in the displayed remainder contains either two factor perturbations or
one perturbation times `ybar-yhat`. -/
theorem higham21_dh1993_factor_difference_identity
    {m : Nat}
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat z : Fin m -> Real)
    (hInv : IsInverse m R Rinv)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat)) :
    rectMatMulVec R (fun i => ybar i - yhat i) =
      fun i =>
        higham21SNEDHFactorLeadingAt
            R Rinv DeltaR1 DeltaR2 ybar z i +
          higham21SNEDHFactorRemainderAt
            R Rinv DeltaR1 DeltaR2 ybar yhat z i := by
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let v : Fin m -> Real :=
    rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat
  let q : Fin m -> Real := fun i =>
    rectMatMulVec DeltaR2 yhat i - rectMatMulVec R d i
  have hRaw :=
    higham21_dh1993_factor_difference_raw
      R Rinv DeltaR1 DeltaR2 ybar yhat hInv hNormal
  have hRd :
      rectMatMulVec R d =
        fun i => rectMatMulVec R ybar i - rectMatMulVec R yhat i := by
    simpa [d] using rectMatMulVec_sub R ybar yhat
  have hv :
      v = fun i => rectMatMulVec R ybar i + q i := by
    rw [show v = rectMatMulVec
      (fun i j => R i j + DeltaR2 i j) yhat by rfl]
    rw [rectMatMulVec_mat_add]
    ext i
    have hi := congrFun hRd i
    dsimp only [q]
    linarith
  have hD1 :
      rectMatMulVec (finiteTranspose DeltaR1) v =
        fun i =>
          rectMatMulVec (finiteTranspose DeltaR1)
              (rectMatMulVec R ybar) i +
            rectMatMulVec (finiteTranspose DeltaR1) q i := by
    rw [hv, rectMatMulVec_add]
  have hLifted :
      rectMatMulVec (finiteTranspose Rinv)
          (rectMatMulVec (finiteTranspose DeltaR1) v) =
        fun i =>
          rectMatMulVec (finiteTranspose Rinv)
              (rectMatMulVec (finiteTranspose DeltaR1)
                (rectMatMulVec R ybar)) i +
            rectMatMulVec (finiteTranspose Rinv)
              (rectMatMulVec (finiteTranspose DeltaR1) q) i := by
    rw [hD1, rectMatMulVec_add]
  have hD2 :
      rectMatMulVec DeltaR2 yhat =
        fun i =>
          rectMatMulVec DeltaR2 z i +
            rectMatMulVec DeltaR2 (fun k => yhat k - z k) i := by
    have hsub := rectMatMulVec_sub DeltaR2 yhat z
    ext i
    have hi := congrFun hsub i
    linarith
  rw [hRaw]
  ext i
  rw [congrFun hD2 i, congrFun hLifted i]
  simp only [higham21SNEDHFactorLeadingAt,
    higham21SNEDHFactorRemainderAt]
  change
    (rectMatMulVec DeltaR2 z i +
        rectMatMulVec DeltaR2 (fun k => yhat k - z k) i) +
      (rectMatMulVec (finiteTranspose Rinv)
          (rectMatMulVec (finiteTranspose DeltaR1)
            (rectMatMulVec R ybar)) i +
        rectMatMulVec (finiteTranspose Rinv)
          (rectMatMulVec (finiteTranspose DeltaR1) q) i) =
      (rectMatMulVec (finiteTranspose Rinv)
          (rectMatMulVec (finiteTranspose DeltaR1)
            (rectMatMulVec R ybar)) i +
        rectMatMulVec DeltaR2 z i) +
      (rectMatMulVec DeltaR2 (fun k => yhat k - z k) i +
        rectMatMulVec (finiteTranspose Rinv)
          (rectMatMulVec (finiteTranspose DeltaR1) q) i)
  ring

/-- Same-right-hand-side wrapper for the pivoted factor identity. -/
theorem higham21_dh1993_factor_difference_identity_of_same_rhs
    {m : Nat}
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (b ybar yhat z : Fin m -> Real)
    (hInv : IsInverse m R Rinv)
    (hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b)
    (hhat :
      rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat) = b) :
    rectMatMulVec R (fun i => ybar i - yhat i) =
      fun i =>
        higham21SNEDHFactorLeadingAt
            R Rinv DeltaR1 DeltaR2 ybar z i +
          higham21SNEDHFactorRemainderAt
            R Rinv DeltaR1 DeltaR2 ybar yhat z i :=
  higham21_dh1993_factor_difference_identity
    R Rinv DeltaR1 DeltaR2 ybar yhat z hInv (hbar.trans hhat.symm)

/-- Signed first-order output correction associated with the pivoted factor
split.  Here `F` is the QR factor perturbation in `B = A + F`, and `g` is the
final rounded transpose-action error. -/
noncomputable def higham21SNEDHSignedFirstOrderAt {m n : Nat}
    (F : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar z : Fin m -> Real) (g : Fin n -> Real) : Fin n -> Real :=
  fun j =>
    -rectMatMulVec Q
        (higham21SNEDHFactorLeadingAt
          R Rinv DeltaR1 DeltaR2 ybar z) j -
      rectTransposeMulVec F ybar j + g j

/-- Exact finite output remainder associated with
`higham21SNEDHSignedFirstOrderAt`. -/
noncomputable def higham21SNEDHSignedRemainderAt {m n : Nat}
    (F : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat z : Fin m -> Real) : Fin n -> Real :=
  fun j =>
    -rectMatMulVec Q
        (higham21SNEDHFactorRemainderAt
          R Rinv DeltaR1 DeltaR2 ybar yhat z) j +
      rectTransposeMulVec F (fun i => ybar i - yhat i) j

/-- Exact signed transfer identity corresponding to Demmel--Higham
(3.14)--(3.17).

If `B = A + F` and `B^T = Q R`, then the difference between the rounded
`A^T*yhat` formation and `B^T*ybar` is the signed first-order term plus the
explicit finite remainder. -/
theorem higham21_dh1993_signed_transfer_identity
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat z : Fin m -> Real) (g : Fin n -> Real)
    (hInv : IsInverse m R Rinv)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat))
    (hFactor :
      finiteTranspose (fun i j => A i j + F i j) = rectMatMul Q R) :
    (fun j =>
      rectTransposeMulVec A yhat j + g j -
        rectTransposeMulVec (fun i j => A i j + F i j) ybar j) =
      fun j =>
        higham21SNEDHSignedFirstOrderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar z g j +
          higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat z j := by
  let B : Fin m -> Fin n -> Real := fun i j => A i j + F i j
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let leading : Fin m -> Real :=
    higham21SNEDHFactorLeadingAt
      R Rinv DeltaR1 DeltaR2 ybar z
  let remainder : Fin m -> Real :=
    higham21SNEDHFactorRemainderAt
      R Rinv DeltaR1 DeltaR2 ybar yhat z
  have hFactorDifference :=
    higham21_dh1993_factor_difference_identity
      R Rinv DeltaR1 DeltaR2 ybar yhat z hInv hNormal
  have hBAction :
      rectTransposeMulVec B d =
        rectMatMulVec Q (rectMatMulVec R d) := by
    change rectMatMulVec (finiteTranspose B) d =
      rectMatMulVec Q (rectMatMulVec R d)
    rw [show finiteTranspose B = rectMatMul Q R by simpa [B] using hFactor]
    exact rectMatMulVec_rectMatMul Q R d
  have hBdiff :
      rectTransposeMulVec B d =
        fun j =>
          rectMatMulVec Q leading j + rectMatMulVec Q remainder j := by
    rw [hBAction]
    rw [show rectMatMulVec R d = fun i => leading i + remainder i by
      simpa [d, leading, remainder] using hFactorDifference]
    exact rectMatMulVec_add Q leading remainder
  have hBsub :
      rectTransposeMulVec B d =
        fun j =>
          rectTransposeMulVec B ybar j - rectTransposeMulVec B yhat j := by
    simpa [d] using higham21Eq21_7_rectTransposeMulVec_sub B ybar yhat
  have hBhat :
      rectTransposeMulVec B yhat =
        fun j =>
          rectTransposeMulVec A yhat j + rectTransposeMulVec F yhat j := by
    ext j
    unfold B rectTransposeMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hFsub :
      rectTransposeMulVec F d =
        fun j =>
          rectTransposeMulVec F ybar j - rectTransposeMulVec F yhat j := by
    simpa [d] using higham21Eq21_7_rectTransposeMulVec_sub F ybar yhat
  ext j
  have hdiffj := congrFun hBdiff j
  rw [congrFun hBsub j] at hdiffj
  have hhatj := congrFun hBhat j
  have hFj := congrFun hFsub j
  simp only [higham21SNEDHSignedFirstOrderAt,
    higham21SNEDHSignedRemainderAt]
  change
    rectTransposeMulVec A yhat j + g j - rectTransposeMulVec B ybar j =
      (-rectMatMulVec Q leading j - rectTransposeMulVec F ybar j + g j) +
        (-rectMatMulVec Q remainder j + rectTransposeMulVec F d j)
  linarith

/-- Economy orthonormality in the rectangular-product notation used by the
SNE signed analysis. -/
theorem higham21_sne_qr_economy_gram_eq_id
    {m n : Nat} (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectMatMul (finiteTranspose Q) Q = idMatrix m := by
  ext i j
  simpa [rectMatMul, finiteTranspose, rectangularGram] using hQ i j

/-- Transposed form of an economy factorization `B^T = Q R`. -/
theorem higham21_sne_qr_transpose_factor
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hFactor : finiteTranspose B = rectMatMul Q R) :
    B = rectMatMul (finiteTranspose R) (finiteTranspose Q) := by
  ext i j
  have hij := congrFun (congrFun hFactor j) i
  unfold finiteTranspose at hij
  rw [hij]
  unfold rectMatMul finiteTranspose
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The Gram matrix of an exact economy factor is `R^T R`. -/
theorem higham21_sne_qr_rectGram_eq
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R) :
    rectGram B = rectMatMul (finiteTranspose R) R := by
  have hB := higham21_sne_qr_transpose_factor B Q R hFactor
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hGramProduct : rectGram B = rectMatMul B (finiteTranspose B) := by
    ext i j
    rfl
  rw [hGramProduct, hFactor, hB]
  calc
    rectMatMul
        (rectMatMul (finiteTranspose R) (finiteTranspose Q))
        (rectMatMul Q R) =
      rectMatMul (finiteTranspose R)
        (rectMatMul (finiteTranspose Q) (rectMatMul Q R)) := by
          exact rectMatMul_assoc
            (finiteTranspose R) (finiteTranspose Q) (rectMatMul Q R)
    _ = rectMatMul (finiteTranspose R)
        (rectMatMul (rectMatMul (finiteTranspose Q) Q) R) := by
          exact congrArg (rectMatMul (finiteTranspose R))
            (rectMatMul_assoc (finiteTranspose Q) Q R).symm
    _ = rectMatMul (finiteTranspose R)
        (rectMatMul (idMatrix m) R) := by rw [hQtQ]
    _ = rectMatMul (finiteTranspose R) R := by rw [rectMatMul_id_left]

/-- Canonical pseudoinverse compatibility with an invertible economy QR
factorization:

`B^+ = Q R^{-T}`.

The canonical Gram pseudoinverse is essential here; a generic right inverse of
`B` need not have this factor form. -/
theorem higham21_sne_qr_pseudoinverse_factor
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R)
    (hInv : IsInverse m R Rinv) :
    undetAplusOfGramNonsingInv B =
      rectMatMul Q (finiteTranspose Rinv) := by
  have hGram := higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hRRinv : rectMatMul R Rinv = idMatrix m := by
    ext i j
    exact hInv.2 i j
  rw [undetAplusOfGramNonsingInv,
    undetAplusOfGramInv_eq_rectMatMul_finiteTranspose]
  rw [hFactor]
  rw [show undetGramNonsingInv B =
      rectMatMul Rinv (finiteTranspose Rinv) by
    unfold undetGramNonsingInv
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv]
  calc
    rectMatMul (rectMatMul Q R)
        (rectMatMul Rinv (finiteTranspose Rinv)) =
      rectMatMul Q
        (rectMatMul R (rectMatMul Rinv (finiteTranspose Rinv))) := by
          exact rectMatMul_assoc Q R
            (rectMatMul Rinv (finiteTranspose Rinv))
    _ = rectMatMul Q
        (rectMatMul (rectMatMul R Rinv) (finiteTranspose Rinv)) := by
          exact congrArg (rectMatMul Q)
            (rectMatMul_assoc R Rinv (finiteTranspose Rinv)).symm
    _ = rectMatMul Q
        (rectMatMul (idMatrix m) (finiteTranspose Rinv)) := by rw [hRRinv]
    _ = rectMatMul Q (finiteTranspose Rinv) := by rw [rectMatMul_id_left]

/-- Absolute-value operator bound for an economy matrix with `m`
orthonormal columns. -/
theorem higham21_sne_abs_economy_rectOpNorm2Le
    {m n : Nat} (hm : 0 < m) (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le (absMatrixRect Q) (Real.sqrt (m : Real)) := by
  classical
  have hrank : realRectMatrixRank Q <= m := by
    unfold realRectMatrixRank complexMatrixRank
    simpa using
      (Matrix.rank_le_card_width
        (realRectToCMatrix Q : Matrix (Fin n) (Fin m) Complex))
  have hsqrt :
      Real.sqrt (realRectMatrixRank Q : Real) <= Real.sqrt (m : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrank)
  have hbase :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm Q (by norm_num : (0 : Real) <= 1) hQ.rectOpNorm2Le_one
  exact rectOpNorm2Le_mono (by simpa only [mul_one] using hsqrt) hbase

/-- Transposed absolute-value operator bound for an economy matrix. -/
theorem higham21_sne_abs_economy_transpose_rectOpNorm2Le
    {m n : Nat} (hm : 0 < m) (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le (absMatrixRect (finiteTranspose Q))
      (Real.sqrt (m : Real)) := by
  have hAbsTranspose :
      absMatrixRect (finiteTranspose Q) =
        finiteTranspose (absMatrixRect Q) := by
    ext i j
    rfl
  rw [hAbsTranspose]
  exact rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    (absMatrixRect Q) (Real.sqrt_nonneg _)
      (higham21_sne_abs_economy_rectOpNorm2Le hm Q hQ)

/-- Absolute values of an exact rectangular product are bounded by the
product of the absolute-value factors. -/
theorem higham21_sne_abs_rectMatMul_entry_le
    {m n p : Nat} (A : Fin m -> Fin n -> Real)
    (B : Fin n -> Fin p -> Real) (i : Fin m) (j : Fin p) :
    absMatrixRect (rectMatMul A B) i j <=
      rectMatMul (absMatrixRect A) (absMatrixRect B) i j := by
  unfold absMatrixRect rectMatMul
  calc
    |∑ k : Fin n, A i k * B k j| <=
        ∑ k : Fin n, |A i k * B k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_congr rfl
      intro k hk
      exact abs_mul (A i k) (B k j)

/-- A componentwise relative matrix perturbation gives the corresponding
absolute matrix-vector majorant. -/
theorem higham21_sne_componentwise_matvec_majorant
    {m n : Nat} (theta : Real)
    (A Delta : Fin m -> Fin n -> Real)
    (hDelta : forall i j, |Delta i j| <= theta * |A i j|)
    (x : Fin n -> Real) (i : Fin m) :
    |rectMatMulVec Delta x i| <=
      theta * rectMatMulVec (absMatrixRect A) (fun j => |x j|) i := by
  calc
    |rectMatMulVec Delta x i| <=
        ∑ j : Fin n, |Delta i j| * |x j| :=
      abs_rectMatMulVec_le Delta x i
    _ <= ∑ j : Fin n, (theta * |A i j|) * |x j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hDelta i j) (abs_nonneg _)
    _ = theta * rectMatMulVec (absMatrixRect A)
        (fun j => |x j|) i := by
      unfold rectMatMulVec absMatrixRect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Demmel--Higham (1993), equation (3.18), in exact finite form.

For the canonical Gram pseudoinverse associated with an economy QR
factorization `B^T = Q R`, the triangular absolute-value condition product is
bounded by `m` times the Chapter 21 row-scaled condition expression. -/
theorem higham21_dh1993_eq3_18
    {m n : Nat} (hm : 0 < m)
    (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R)
    (hInv : IsInverse m R Rinv) :
    rectOpNorm2Le
      (rectMatMul
        (absMatrixRect (finiteTranspose Rinv))
        (absMatrixRect (finiteTranspose R)))
      ((m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B)) := by
  let P : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv B
  let C : Fin n -> Fin n -> Real :=
    rectMatMul (absMatrixRect P) (absMatrixRect B)
  let D : Fin m -> Fin m -> Real :=
    rectMatMul (absMatrixRect (finiteTranspose Q))
      (rectMatMul C (absMatrixRect Q))
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hP : P = rectMatMul Q (finiteTranspose Rinv) := by
    simpa [P] using
      higham21_sne_qr_pseudoinverse_factor B Q R Rinv hQ hFactor hInv
  have hRinvT :
      finiteTranspose Rinv =
        rectMatMul (finiteTranspose Q) P := by
    rw [hP]
    symm
    calc
      rectMatMul (finiteTranspose Q)
          (rectMatMul Q (finiteTranspose Rinv)) =
        rectMatMul
          (rectMatMul (finiteTranspose Q) Q)
          (finiteTranspose Rinv) := by
            exact (rectMatMul_assoc
              (finiteTranspose Q) Q (finiteTranspose Rinv)).symm
      _ = rectMatMul (idMatrix m) (finiteTranspose Rinv) := by
        rw [hQtQ]
      _ = finiteTranspose Rinv := rectMatMul_id_left _
  have hB := higham21_sne_qr_transpose_factor B Q R hFactor
  have hRT :
      finiteTranspose R = rectMatMul B Q := by
    rw [hB]
    symm
    calc
      rectMatMul
          (rectMatMul (finiteTranspose R) (finiteTranspose Q)) Q =
        rectMatMul (finiteTranspose R)
          (rectMatMul (finiteTranspose Q) Q) := by
            exact rectMatMul_assoc
              (finiteTranspose R) (finiteTranspose Q) Q
      _ = rectMatMul (finiteTranspose R) (idMatrix m) := by
        rw [hQtQ]
      _ = finiteTranspose R := rectMatMul_id_right _
  have hleft : forall i k,
      absMatrixRect (finiteTranspose Rinv) i k <=
        rectMatMul
          (absMatrixRect (finiteTranspose Q)) (absMatrixRect P) i k := by
    intro i k
    rw [hRinvT]
    exact higham21_sne_abs_rectMatMul_entry_le
      (finiteTranspose Q) P i k
  have hright : forall k j,
      absMatrixRect (finiteTranspose R) k j <=
        rectMatMul (absMatrixRect B) (absMatrixRect Q) k j := by
    intro k j
    rw [hRT]
    exact higham21_sne_abs_rectMatMul_entry_le B Q k j
  have hmajor : forall i j,
      |rectMatMul
          (absMatrixRect (finiteTranspose Rinv))
          (absMatrixRect (finiteTranspose R)) i j| <= D i j := by
    intro i j
    have hnonneg :
        0 <= rectMatMul
          (absMatrixRect (finiteTranspose Rinv))
          (absMatrixRect (finiteTranspose R)) i j := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnonneg]
    calc
      rectMatMul
          (absMatrixRect (finiteTranspose Rinv))
          (absMatrixRect (finiteTranspose R)) i j <=
        ∑ k : Fin m,
          rectMatMul
              (absMatrixRect (finiteTranspose Q)) (absMatrixRect P) i k *
            absMatrixRect (finiteTranspose R) k j := by
              unfold rectMatMul
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_right
                (hleft i k) (abs_nonneg _)
      _ <= ∑ k : Fin m,
          rectMatMul
              (absMatrixRect (finiteTranspose Q)) (absMatrixRect P) i k *
            rectMatMul
              (absMatrixRect B) (absMatrixRect Q) k j := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (hright k j)
                (Finset.sum_nonneg fun l hl =>
                  mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = D i j := by
        change
          rectMatMul
              (rectMatMul
                (absMatrixRect (finiteTranspose Q)) (absMatrixRect P))
              (rectMatMul (absMatrixRect B) (absMatrixRect Q)) i j =
            D i j
        dsimp only [D, C]
        rw [rectMatMul_assoc
          (absMatrixRect (finiteTranspose Q)) (absMatrixRect P)
          (rectMatMul (absMatrixRect B) (absMatrixRect Q))]
        rw [← rectMatMul_assoc
          (absMatrixRect P) (absMatrixRect B) (absMatrixRect Q)]
  have hC : rectOpNorm2Le C
      (higham21Cond2With B (undetAplusOfGramNonsingInv B)) := by
    simpa [C, P, higham21Cond2With] using
      (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl)
  have hQabs := higham21_sne_abs_economy_rectOpNorm2Le hm Q hQ
  have hQTabs :=
    higham21_sne_abs_economy_transpose_rectOpNorm2Le hm Q hQ
  have hCQ :
      rectOpNorm2Le (rectMatMul C (absMatrixRect Q))
        (higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          Real.sqrt (m : Real)) :=
    rectOpNorm2Le_rectMatMul C (absMatrixRect Q)
      (higham21Cond2With_nonneg B (undetAplusOfGramNonsingInv B))
      hC hQabs
  have hD : rectOpNorm2Le D
      (Real.sqrt (m : Real) *
        (higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          Real.sqrt (m : Real))) := by
    exact rectOpNorm2Le_rectMatMul
      (absMatrixRect (finiteTranspose Q))
      (rectMatMul C (absMatrixRect Q))
      (Real.sqrt_nonneg _) hQTabs hCQ
  have hsqrtSq : Real.sqrt (m : Real) ^ 2 = (m : Real) :=
    Real.sq_sqrt (by positivity)
  apply rectOpNorm2Le_of_abs_entry_le hmajor
  apply rectOpNorm2Le_mono _ hD
  calc
    Real.sqrt (m : Real) *
        (higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          Real.sqrt (m : Real)) =
      Real.sqrt (m : Real) ^ 2 *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) := by ring
    _ = (m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) := by
      rw [hsqrtSq]
    _ <= (m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) := le_rfl

/-- Demmel--Higham (1993), equation (3.20), in exact finite form.

The factorization `B^T = Q R` and the canonical pseudoinverse identify
`ybar = (B^+)^T xbar`.  Equation (3.19), supplied by
`higham21_sne_dual_majorant_le_cond2`, then gives the inner condition bound;
the sole additional factor is `|| |Q^T| ||_2 <= sqrt m`. -/
theorem higham21_dh1993_eq3_20
    {m n : Nat} (hm : 0 < m)
    (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv : Fin m -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R)
    (hInv : IsInverse m R Rinv)
    (hxbar : xbar = rectTransposeMulVec B ybar) :
    vecNorm2
        (rectMatMulVec (absMatrixRect R) (fun i => |ybar i|)) <=
      Real.sqrt (m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
  let P : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv B
  let yabs : Fin m -> Real := fun i => |ybar i|
  let w : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect B) yabs
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hP : P = rectMatMul Q (finiteTranspose Rinv) := by
    simpa [P] using
      higham21_sne_qr_pseudoinverse_factor B Q R Rinv hQ hFactor hInv
  have hB := higham21_sne_qr_transpose_factor B Q R hFactor
  have hTInv := isInverse_finiteTranspose hInv
  have hRight : rectMatMul B P = idMatrix m := by
    rw [hB, hP]
    calc
      rectMatMul
          (rectMatMul (finiteTranspose R) (finiteTranspose Q))
          (rectMatMul Q (finiteTranspose Rinv)) =
        rectMatMul (finiteTranspose R)
          (rectMatMul (finiteTranspose Q)
            (rectMatMul Q (finiteTranspose Rinv))) := by
              exact rectMatMul_assoc
                (finiteTranspose R) (finiteTranspose Q)
                (rectMatMul Q (finiteTranspose Rinv))
      _ = rectMatMul (finiteTranspose R)
          (rectMatMul
            (rectMatMul (finiteTranspose Q) Q)
            (finiteTranspose Rinv)) := by
              rw [← rectMatMul_assoc
                (finiteTranspose Q) Q (finiteTranspose Rinv)]
      _ = rectMatMul (finiteTranspose R)
          (rectMatMul (idMatrix m) (finiteTranspose Rinv)) := by
              rw [hQtQ]
      _ = rectMatMul (finiteTranspose R) (finiteTranspose Rinv) := by
              rw [rectMatMul_id_left]
      _ = idMatrix m := by
        ext i j
        exact hTInv.2 i j
  have hybar : ybar = rectTransposeMulVec P xbar := by
    have hleft :=
      higham21_theorem21_1_transpose_left_inverse_of_right_inverse
        B P hRight ybar
    calc
      ybar = rectMatMulVec (finiteTranspose P)
          (rectMatMulVec (finiteTranspose B) ybar) := hleft.symm
      _ = rectTransposeMulVec P xbar := by
        change rectMatMulVec (finiteTranspose P)
            (rectTransposeMulVec B ybar) =
          rectMatMulVec (finiteTranspose P) xbar
        rw [← hxbar]
  have hR : R = rectMatMul (finiteTranspose Q) (finiteTranspose B) := by
    rw [hFactor]
    symm
    calc
      rectMatMul (finiteTranspose Q) (rectMatMul Q R) =
        rectMatMul
          (rectMatMul (finiteTranspose Q) Q) R := by
            exact (rectMatMul_assoc (finiteTranspose Q) Q R).symm
      _ = rectMatMul (idMatrix m) R := by rw [hQtQ]
      _ = R := rectMatMul_id_left _
  have hRmajor : forall i k,
      absMatrixRect R i k <=
        rectMatMul
          (absMatrixRect (finiteTranspose Q))
          (absMatrixRect (finiteTranspose B)) i k := by
    intro i k
    rw [hR]
    exact higham21_sne_abs_rectMatMul_entry_le
      (finiteTranspose Q) (finiteTranspose B) i k
  have hpoint : forall i,
      |rectMatMulVec (absMatrixRect R) yabs i| <=
        rectMatMulVec (absMatrixRect (finiteTranspose Q)) w i := by
    intro i
    have hnonneg :
        0 <= rectMatMulVec (absMatrixRect R) yabs i := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [abs_of_nonneg hnonneg]
    calc
      rectMatMulVec (absMatrixRect R) yabs i <=
        ∑ k : Fin m,
          rectMatMul
              (absMatrixRect (finiteTranspose Q))
              (absMatrixRect (finiteTranspose B)) i k * yabs k := by
                unfold rectMatMulVec
                apply Finset.sum_le_sum
                intro k hk
                exact mul_le_mul_of_nonneg_right
                  (hRmajor i k) (abs_nonneg _)
      _ = rectMatMulVec
          (rectMatMul
            (absMatrixRect (finiteTranspose Q))
            (absMatrixRect (finiteTranspose B))) yabs i := rfl
      _ = rectMatMulVec (absMatrixRect (finiteTranspose Q))
          (rectMatMulVec (absMatrixRect (finiteTranspose B)) yabs) i := by
            rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec (absMatrixRect (finiteTranspose Q)) w i := by
        rfl
  have hw : vecNorm2 w <=
      higham21Cond2With B (undetAplusOfGramNonsingInv B) *
        vecNorm2 xbar := by
    simpa [w, yabs, P, hybar] using
      (higham21_sne_dual_majorant_le_cond2
        B (undetAplusOfGramNonsingInv B) xbar)
  have hQTabs :=
    higham21_sne_abs_economy_transpose_rectOpNorm2Le hm Q hQ
  calc
    vecNorm2
        (rectMatMulVec (absMatrixRect R) (fun i => |ybar i|)) =
      vecNorm2 (rectMatMulVec (absMatrixRect R) yabs) := by rfl
    _ <= vecNorm2
        (rectMatMulVec (absMatrixRect (finiteTranspose Q)) w) :=
      vecNorm2_le_of_abs_le
        (rectMatMulVec (absMatrixRect R) yabs)
        (rectMatMulVec (absMatrixRect (finiteTranspose Q)) w)
        hpoint
    _ <= Real.sqrt (m : Real) * vecNorm2 w := hQTabs w
    _ <= Real.sqrt (m : Real) *
        (higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar) :=
      mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _)
    _ = Real.sqrt (m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring

/-- Source-faithful first-order factorwise SNE bound.

Under componentwise relative bounds on the two triangular-solve
perturbations, the pivot-`ybar` leading term from (3.17) contributes at most
`theta * (m + sqrt m) * cond2(B) * ||xbar||_2`.  The two constants arise
separately from (3.18) and (3.20); no aggregate Gram-envelope condition factor
is introduced. -/
theorem higham21_dh1993_firstOrder_factor_bound
    {m n : Nat} (hm : 0 < m)
    (theta : Real) (htheta : 0 <= theta)
    (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R)
    (hInv : IsInverse m R Rinv)
    (hxbar : xbar = rectTransposeMulVec B ybar)
    (hDeltaR1 : forall i j, |DeltaR1 i j| <= theta * |R i j|)
    (hDeltaR2 : forall i j, |DeltaR2 i j| <= theta * |R i j|) :
    vecNorm2
        (rectMatMulVec Q
          (higham21SNEDHFactorLeadingAt
            R Rinv DeltaR1 DeltaR2 ybar ybar)) <=
      theta * ((m : Real) + Real.sqrt (m : Real)) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
  let v : Fin m -> Real := rectMatMulVec R ybar
  let vabs : Fin m -> Real := fun i => |v i|
  let u1 : Fin m -> Real :=
    rectMatMulVec (finiteTranspose DeltaR1) v
  let t1 : Fin m -> Real :=
    rectMatMulVec (finiteTranspose Rinv) u1
  let t2 : Fin m -> Real := rectMatMulVec DeltaR2 ybar
  let M : Fin m -> Fin m -> Real :=
    rectMatMul
      (absMatrixRect (finiteTranspose Rinv))
      (absMatrixRect (finiteTranspose R))
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q
      (by norm_num) hQ.rectOpNorm2Le_one
  have hrecover :
      rectMatMulVec (finiteTranspose Q) (rectMatMulVec Q v) = v := by
    rw [← rectMatMulVec_rectMatMul, hQtQ, rectMatMulVec_idMatrix]
  have hQisometry :
      vecNorm2 (rectMatMulVec Q v) = vecNorm2 v := by
    apply le_antisymm
    · simpa using hQ.rectOpNorm2Le_one v
    · calc
        vecNorm2 v = vecNorm2
            (rectMatMulVec (finiteTranspose Q) (rectMatMulVec Q v)) := by
              rw [hrecover]
        _ <= 1 * vecNorm2 (rectMatMulVec Q v) := hQT _
        _ = vecNorm2 (rectMatMulVec Q v) := one_mul _
  have hxv : xbar = rectMatMulVec Q v := by
    calc
      xbar = rectMatMulVec (finiteTranspose B) ybar := hxbar
      _ = rectMatMulVec (rectMatMul Q R) ybar := by rw [hFactor]
      _ = rectMatMulVec Q (rectMatMulVec R ybar) := by
        rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Q v := by rfl
  have hvNorm : vecNorm2 v = vecNorm2 xbar := by
    calc
      vecNorm2 v = vecNorm2 (rectMatMulVec Q v) := hQisometry.symm
      _ = vecNorm2 xbar := by rw [hxv]
  have hvabsNorm : vecNorm2 vabs = vecNorm2 xbar := by
    calc
      vecNorm2 vabs = vecNorm2 v := by
        simpa [vabs] using vecNorm2_abs v
      _ = vecNorm2 xbar := hvNorm
  have hDeltaR1T : forall i j,
      |finiteTranspose DeltaR1 i j| <=
        theta * |finiteTranspose R i j| := by
    intro i j
    simpa [finiteTranspose] using hDeltaR1 j i
  have hu1 : forall i,
      |u1 i| <= theta *
        rectMatMulVec (absMatrixRect (finiteTranspose R)) vabs i := by
    intro i
    simpa [u1, vabs] using
      higham21_sne_componentwise_matvec_majorant
        theta (finiteTranspose R) (finiteTranspose DeltaR1)
          hDeltaR1T v i
  have ht1point : forall i,
      |t1 i| <= theta * rectMatMulVec M vabs i := by
    intro i
    calc
      |t1 i| <= ∑ k : Fin m,
          |finiteTranspose Rinv i k| * |u1 k| := by
            simpa [t1] using
              abs_rectMatMulVec_le (finiteTranspose Rinv) u1 i
      _ <= ∑ k : Fin m,
          |finiteTranspose Rinv i k| *
            (theta *
              rectMatMulVec
                (absMatrixRect (finiteTranspose R)) vabs k) := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (hu1 k) (abs_nonneg _)
      _ = theta * rectMatMulVec M vabs i := by
        rw [show rectMatMulVec M vabs =
            rectMatMulVec (absMatrixRect (finiteTranspose Rinv))
              (rectMatMulVec
                (absMatrixRect (finiteTranspose R)) vabs) by
          exact rectMatMulVec_rectMatMul
            (absMatrixRect (finiteTranspose Rinv))
            (absMatrixRect (finiteTranspose R)) vabs]
        unfold rectMatMulVec absMatrixRect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hM := higham21_dh1993_eq3_18
    hm B Q R Rinv hQ hFactor hInv
  have ht1Norm : vecNorm2 t1 <=
      theta * ((m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
          vecNorm2 xbar := by
    calc
      vecNorm2 t1 <=
          vecNorm2 (fun i => theta * rectMatMulVec M vabs i) :=
        vecNorm2_le_of_abs_le t1
          (fun i => theta * rectMatMulVec M vabs i) ht1point
      _ = theta * vecNorm2 (rectMatMulVec M vabs) := by
        rw [vecNorm2_smul, abs_of_nonneg htheta]
      _ <= theta *
          (((m : Real) *
              higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
            vecNorm2 vabs) :=
        mul_le_mul_of_nonneg_left (hM vabs) htheta
      _ = theta * ((m : Real) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
            vecNorm2 xbar := by rw [hvabsNorm]; ring
  have ht2point : forall i,
      |t2 i| <= theta *
        rectMatMulVec (absMatrixRect R) (fun k => |ybar k|) i := by
    intro i
    simpa [t2] using
      higham21_sne_componentwise_matvec_majorant
        theta R DeltaR2 hDeltaR2 ybar i
  have hRbar := higham21_dh1993_eq3_20
    hm B Q R Rinv ybar xbar hQ hFactor hInv hxbar
  have ht2Norm : vecNorm2 t2 <=
      theta * (Real.sqrt (m : Real) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
          vecNorm2 xbar := by
    calc
      vecNorm2 t2 <=
          vecNorm2 (fun i => theta *
            rectMatMulVec (absMatrixRect R) (fun k => |ybar k|) i) :=
        vecNorm2_le_of_abs_le t2
          (fun i => theta *
            rectMatMulVec (absMatrixRect R) (fun k => |ybar k|) i)
          ht2point
      _ = theta * vecNorm2
          (rectMatMulVec (absMatrixRect R) (fun k => |ybar k|)) := by
        rw [vecNorm2_smul, abs_of_nonneg htheta]
      _ <= theta *
          (Real.sqrt (m : Real) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
              vecNorm2 xbar) :=
        mul_le_mul_of_nonneg_left hRbar htheta
      _ = theta * (Real.sqrt (m : Real) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
            vecNorm2 xbar := by ring
  have hleading :
      higham21SNEDHFactorLeadingAt
          R Rinv DeltaR1 DeltaR2 ybar ybar =
        fun i => t1 i + t2 i := by
    rfl
  calc
    vecNorm2
        (rectMatMulVec Q
          (higham21SNEDHFactorLeadingAt
            R Rinv DeltaR1 DeltaR2 ybar ybar)) <=
      1 * vecNorm2
        (higham21SNEDHFactorLeadingAt
          R Rinv DeltaR1 DeltaR2 ybar ybar) :=
      hQ.rectOpNorm2Le_one _
    _ = vecNorm2
        (higham21SNEDHFactorLeadingAt
          R Rinv DeltaR1 DeltaR2 ybar ybar) := one_mul _
    _ <= vecNorm2 t1 + vecNorm2 t2 := by
      rw [hleading]
      exact vecNorm2_add_le t1 t2
    _ <= theta * ((m : Real) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
          vecNorm2 xbar +
        theta * (Real.sqrt (m : Real) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B)) *
          vecNorm2 xbar := add_le_add ht1Norm ht2Norm
    _ = theta * ((m : Real) + Real.sqrt (m : Real)) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring

/-- Finite signed SNE output bound obtained from the Demmel--Higham
factorwise cancellation.  Unlike the earlier aggregate-envelope transfer,
this theorem does not assume the desired forward bound.  Its remaining
premises are local estimates for the QR perturbation, the final rounded
transpose action, and the explicitly displayed higher-order remainder.

The conclusion keeps the three first-order sources separate: the two
triangular solves contribute `m + sqrt m`, while `cF` and `cg` record the QR
and final-formation coefficients. -/
theorem higham21_dh1993_signed_output_bound
    {m n : Nat} (hm : 0 < m)
    (theta cF cg C : Real)
    (htheta : 0 <= theta)
    (A F : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat : Fin m -> Real) (xbar : Fin n -> Real)
    (g : Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor :
      finiteTranspose (fun i j => A i j + F i j) = rectMatMul Q R)
    (hInv : IsInverse m R Rinv)
    (hxbar :
      xbar = rectTransposeMulVec (fun i j => A i j + F i j) ybar)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat))
    (hDeltaR1 : forall i j, |DeltaR1 i j| <= theta * |R i j|)
    (hDeltaR2 : forall i j, |DeltaR2 i j| <= theta * |R i j|)
    (hF :
      vecNorm2 (rectTransposeMulVec F ybar) <=
        theta * cF *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
          vecNorm2 xbar)
    (hg :
      vecNorm2 g <=
        theta * cg *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
          vecNorm2 xbar)
    (hrem :
      vecNorm2
        (higham21SNEDHSignedRemainderAt
          F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <= theta ^ 2 * C) :
    vecNorm2 (fun j =>
        rectTransposeMulVec A yhat j + g j - xbar j) <=
      theta * ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
          vecNorm2 xbar +
        theta ^ 2 * C := by
  let B : Fin m -> Fin n -> Real := fun i j => A i j + F i j
  let lead : Fin m -> Real :=
    higham21SNEDHFactorLeadingAt
      R Rinv DeltaR1 DeltaR2 ybar ybar
  let first : Fin n -> Real := fun j =>
    -rectMatMulVec Q lead j - rectTransposeMulVec F ybar j + g j
  let rem : Fin n -> Real :=
    higham21SNEDHSignedRemainderAt
      F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar
  have hid := higham21_dh1993_signed_transfer_identity
    A F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar g hInv hNormal hFactor
  have hlead :
      vecNorm2 (rectMatMulVec Q lead) <=
        theta * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar := by
    simpa [B, lead] using
      higham21_dh1993_firstOrder_factor_bound
        hm theta htheta B Q R Rinv DeltaR1 DeltaR2 ybar xbar
          hQ hFactor hInv hxbar hDeltaR1 hDeltaR2
  have hfirst :
      vecNorm2 first <=
        theta * ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar := by
    have htri1 := vecNorm2_add_le
      (fun j => -rectMatMulVec Q lead j)
      (fun j => -rectTransposeMulVec F ybar j)
    have htri2 := vecNorm2_add_le
      (fun j => -rectMatMulVec Q lead j - rectTransposeMulVec F ybar j) g
    have hsum :
        vecNorm2 first <=
          vecNorm2 (rectMatMulVec Q lead) +
            vecNorm2 (rectTransposeMulVec F ybar) + vecNorm2 g := by
      calc
        vecNorm2 first <=
            vecNorm2
                (fun j => -rectMatMulVec Q lead j -
                  rectTransposeMulVec F ybar j) + vecNorm2 g := by
              simpa [first] using htri2
        _ <= (vecNorm2 (rectMatMulVec Q lead) +
              vecNorm2 (rectTransposeMulVec F ybar)) + vecNorm2 g := by
              gcongr
              simpa [vecNorm2_neg] using htri1
        _ = vecNorm2 (rectMatMulVec Q lead) +
              vecNorm2 (rectTransposeMulVec F ybar) + vecNorm2 g := rfl
    calc
      vecNorm2 first <=
          vecNorm2 (rectMatMulVec Q lead) +
            vecNorm2 (rectTransposeMulVec F ybar) + vecNorm2 g := hsum
      _ <=
          (theta * ((m : Real) + Real.sqrt (m : Real)) *
              higham21Cond2With B (undetAplusOfGramNonsingInv B) *
                vecNorm2 xbar) +
            (theta * cF *
              higham21Cond2With B (undetAplusOfGramNonsingInv B) *
                vecNorm2 xbar) +
            (theta * cg *
              higham21Cond2With B (undetAplusOfGramNonsingInv B) *
                vecNorm2 xbar) := by
          exact add_le_add (add_le_add hlead (by simpa [B] using hF))
            (by simpa [B] using hg)
      _ = theta * ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
              vecNorm2 xbar := by ring
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => first j + rem j := by
    have hx :
        (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
          fun j =>
            rectTransposeMulVec A yhat j + g j -
              rectTransposeMulVec B ybar j := by
      ext j
      rw [hxbar]
    rw [hx]
    simpa [B, first, rem, lead,
      higham21SNEDHSignedFirstOrderAt] using hid
  rw [herr]
  calc
    vecNorm2 (fun j => first j + rem j) <=
        vecNorm2 first + vecNorm2 rem := vecNorm2_add_le first rem
    _ <= theta * ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar + theta ^ 2 * C :=
      add_le_add hfirst (by simpa [rem] using hrem)
    _ = theta * ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
            vecNorm2 xbar + theta ^ 2 * C := by rfl

end NumStability
