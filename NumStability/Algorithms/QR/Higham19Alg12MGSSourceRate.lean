import NumStability.Algorithms.QR.Higham19Alg12MGSPaddedClosure
import NumStability.Algorithms.LeastSquares.Higham20MPProse

/-!
# Higham Theorem 19.13: source-condition-number rate

This module converts the exact all-orders literal-MGS certificate into the
source-facing `u * kappa_2(A)` form.  The condition number is formed with a
genuine left inverse of the original full-column-rank matrix; the canonical
wrapper below chooses the Moore--Penrose Gram formula.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- The rectangular spectral condition number represented by a supplied
left inverse.  With the canonical Moore--Penrose inverse this is exactly
Higham's `kappa_2(A)`. -/
def mgsSourceKappa2With {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A) *
    complexMatrixOp2 (realRectToCMatrix Aplus)

theorem mgsSourceKappa2With_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real) :
    0 <= mgsSourceKappa2With A Aplus := by
  exact mul_nonneg (complexMatrixOp2_nonneg _) (complexMatrixOp2_nonneg _)

/-- A column-count spectral bound implies the standard Frobenius bound. -/
theorem frobNormRect_le_sqrt_card_mul_of_rectOpNorm2Le {m n : Nat}
    (A : Fin m -> Fin n -> Real) {a : Real} (ha : 0 <= a)
    (hA : rectOpNorm2Le A a) :
    frobNormRect A <= Real.sqrt (n : Real) * a := by
  have hsq0 := frobNormSqRect_le_card_mul_sq_of_rectOpNorm2Le A ha hA
  have hn0 : 0 <= (n : Real) := by positivity
  have hrhs0 : 0 <= Real.sqrt (n : Real) * a :=
    mul_nonneg (Real.sqrt_nonneg _) ha
  have hsq :
      frobNormSqRect A <= (Real.sqrt (n : Real) * a) ^ 2 := by
    calc
      frobNormSqRect A <= (n : Real) * a ^ 2 := hsq0
      _ = (Real.sqrt (n : Real) * a) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn0]
  have hsqrt := Real.sqrt_le_sqrt hsq
  change Real.sqrt (frobNormSqRect A) <= _
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs0] at hsqrt
  exact hsqrt

/-- If `Aplus*A=I`, `A+dA=Q*R`, `Q` has orthonormal columns, and `Rinv` is
a right inverse of `R`, then a small `Aplus*dA` controls `Rinv`.  This is the
finite-dimensional perturbation step used in Higham's proof of (19.30). -/
theorem repaired_qr_right_inverse_rectOpNorm2Le_of_source_left_inverse
    {m n : Nat}
    (A dA Q : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (R Rinv : Fin n -> Fin n -> Real)
    {rho eta : Real}
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hfactor : (fun i j => A i j + dA i j) = rectMatMul Q R)
    (hRright : rectMatMul R Rinv = idMatrix n)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hrho : 0 <= rho) (heta : 0 <= eta)
    (hAplus : rectOpNorm2Le Aplus rho)
    (hdA : rectOpNorm2Le dA eta)
    (hsmall : rho * eta < 1) :
    rectOpNorm2Le Rinv (rho / (1 - rho * eta)) := by
  have hQeq : Q = rectMatMul (fun i j => A i j + dA i j) Rinv := by
    calc
      Q = rectMatMul Q (idMatrix n) := (rectMatMul_id_right Q).symm
      _ = rectMatMul Q (rectMatMul R Rinv) := by rw [hRright]
      _ = rectMatMul (rectMatMul Q R) Rinv :=
        (rectMatMul_assoc Q R Rinv).symm
      _ = rectMatMul (fun i j => A i j + dA i j) Rinv := by rw [hfactor]
  have hsum :
      rectMatMul Aplus Q =
        fun i j => Rinv i j + rectMatMul (rectMatMul Aplus dA) Rinv i j := by
    calc
      rectMatMul Aplus Q =
          rectMatMul Aplus
            (rectMatMul (fun i j => A i j + dA i j) Rinv) := by rw [hQeq]
      _ = rectMatMul
            (rectMatMul Aplus (fun i j => A i j + dA i j)) Rinv :=
          (rectMatMul_assoc Aplus (fun i j => A i j + dA i j) Rinv).symm
      _ = rectMatMul
            (fun i j => rectMatMul Aplus A i j + rectMatMul Aplus dA i j)
            Rinv := by rw [rectMatMul_add_right]
      _ = fun i j =>
            rectMatMul (rectMatMul Aplus A) Rinv i j +
              rectMatMul (rectMatMul Aplus dA) Rinv i j := by
          rw [rectMatMul_add_left]
      _ = fun i j => Rinv i j +
            rectMatMul (rectMatMul Aplus dA) Rinv i j := by
          rw [hleft, rectMatMul_id_left]
  have hQop : rectOpNorm2Le Q 1 := hQ.rectOpNorm2Le_one
  have hAplusQ : rectOpNorm2Le (rectMatMul Aplus Q) (rho * 1) :=
    rectOpNorm2Le_rectMatMul Aplus Q hrho hAplus hQop
  have hAplusdA : rectOpNorm2Le (rectMatMul Aplus dA) (rho * eta) :=
    rectOpNorm2Le_rectMatMul Aplus dA hrho hAplus hdA
  have hden : 0 < 1 - rho * eta := by linarith
  intro x
  let y : Fin n -> Real := rectMatMulVec Rinv x
  let z : Fin n -> Real := rectMatMulVec (rectMatMul Aplus dA) y
  have haction : rectMatMulVec (rectMatMul Aplus Q) x = fun i => y i + z i := by
    rw [hsum]
    calc
      rectMatMulVec
          (fun i j => Rinv i j +
            rectMatMul (rectMatMul Aplus dA) Rinv i j) x =
          fun i => rectMatMulVec Rinv x i +
            rectMatMulVec (rectMatMul (rectMatMul Aplus dA) Rinv) x i :=
        rectMatMulVec_mat_add Rinv
          (rectMatMul (rectMatMul Aplus dA) Rinv) x
      _ = fun i => y i + z i := by
        rw [rectMatMulVec_rectMatMul]
  have hyEq : y = fun i => rectMatMulVec (rectMatMul Aplus Q) x i - z i := by
    ext i
    have hi := congrFun haction i
    linarith
  have hytri : vecNorm2 y <=
      vecNorm2 (rectMatMulVec (rectMatMul Aplus Q) x) + vecNorm2 z := by
    calc
      vecNorm2 y = vecNorm2
          (fun i => rectMatMulVec (rectMatMul Aplus Q) x i + (-z i)) := by
        rw [hyEq]
        congr 1
      _ <= vecNorm2 (rectMatMulVec (rectMatMul Aplus Q) x) +
          vecNorm2 (fun i => -z i) := vecNorm2_add_le _ _
      _ = vecNorm2 (rectMatMulVec (rectMatMul Aplus Q) x) + vecNorm2 z := by
        rw [vecNorm2_neg]
  have hz : vecNorm2 z <= (rho * eta) * vecNorm2 y := by
    simpa [z] using hAplusdA y
  have hraw : vecNorm2 y <= rho * vecNorm2 x +
      (rho * eta) * vecNorm2 y := by
    calc
      vecNorm2 y <=
          vecNorm2 (rectMatMulVec (rectMatMul Aplus Q) x) + vecNorm2 z := hytri
      _ <= (rho * 1) * vecNorm2 x + (rho * eta) * vecNorm2 y :=
        add_le_add (hAplusQ x) hz
      _ = rho * vecNorm2 x + (rho * eta) * vecNorm2 y := by ring
  have hscaled : (1 - rho * eta) * vecNorm2 y <= rho * vecNorm2 x := by
    linarith
  calc
    vecNorm2 (rectMatMulVec Rinv x) = vecNorm2 y := rfl
    _ <= (rho * vecNorm2 x) / (1 - rho * eta) :=
      (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
    _ = (rho / (1 - rho * eta)) * vecNorm2 x := by ring

/-- Exact source-conditioning radius obtained from the two MGS perturbation
channels and the inverse perturbation denominator in Higham's proof. -/
def mgsSourceOrthogonalityRadius {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (c1 c3 : Real) : Real :=
  (Real.sqrt (n : Real) * (c1 + c3) * fp.u *
      mgsSourceKappa2With A Aplus) /
    (1 - Real.sqrt (n : Real) * c3 * fp.u *
      mgsSourceKappa2With A Aplus)

/-- Source-rate package for the literal MGS executor. -/
structure LiteralMGSTheorem1913SourceRateCertificate
    (m n : Nat) (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (c1 c3 : Real) : Prop where
  upper : IsUpperTrapezoidal n n (fl_modifiedGramSchmidtR fp A)
  eq19_29_product_identity : forall i j,
    A i j +
        mgsRoundedProductResidual A
          (fl_modifiedGramSchmidtQ fp A)
          (fl_modifiedGramSchmidtR fp A) i j =
      matMulRect m n n (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A) i j
  eq19_29_product_op2_bound :
    rectOpNorm2Le
      (mgsRoundedProductResidual A
        (fl_modifiedGramSchmidtQ fp A)
        (fl_modifiedGramSchmidtR fp A))
      (Real.sqrt (n : Real) * c1 * fp.u *
        complexMatrixOp2 (realRectToCMatrix A))
  eq19_30_orthogonality :
    opNorm2Le
      (gramSchmidtOrthogonalityResidual
        (fl_modifiedGramSchmidtQ fp A))
      (2 * mgsSourceOrthogonalityRadius fp A Aplus c1 c3 +
        (mgsSourceOrthogonalityRadius fp A Aplus c1 c3) ^ 2)
  eq19_31_repaired_factorization :
    exists (Qrepair : Fin m -> Fin n -> Real)
        (dA2 : Fin m -> Fin n -> Real),
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair (fl_modifiedGramSchmidtR fp A) /\
      (forall j : Fin n,
        columnFrob dA2 j <= c3 * fp.u * columnFrob A j)

/-- The literal executor implies the printed source-rate package once its two
dimension/model coefficients have been compressed to `c1*u` and `c3*u`.
Unlike the earlier fallback route, the denominator below uses a left inverse
of the original matrix `A`, not the inverse of the computed `Rhat`. -/
theorem higham19_13_literal_mgs_source_rate_of_coefficient_bounds
    {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (c1 c3 : Real)
    (hnm : n <= m)
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hc1 : 0 <= c1) (hc3 : 0 <= c3)
    (hproductCoeff : mgsProductGlobalCoeff fp m n <= c1 * fp.u)
    (hrepairCoeff :
      2 * mgsPaddedAccumulatedCoeff fp m n <= c3 * fp.u)
    (hsmall :
      Real.sqrt (n : Real) * c3 * fp.u *
          mgsSourceKappa2With A Aplus < 1) :
    LiteralMGSTheorem1913SourceRateCertificate
      m n fp A Aplus c1 c3 := by
  let Qhat := fl_modifiedGramSchmidtQ fp A
  let Rhat := fl_modifiedGramSchmidtR fp A
  let E := mgsRoundedProductResidual A Qhat Rhat
  let Rinv := nonsingInv n Rhat
  let normA := complexMatrixOp2 (realRectToCMatrix A)
  let rhoA := complexMatrixOp2 (realRectToCMatrix Aplus)
  let kappaA := mgsSourceKappa2With A Aplus
  let etaE := Real.sqrt (n : Real) * c1 * fp.u * normA
  let etaD := Real.sqrt (n : Real) * c3 * fp.u * normA
  have hnormA0 : 0 <= normA := complexMatrixOp2_nonneg _
  have hrhoA0 : 0 <= rhoA := complexMatrixOp2_nonneg _
  have hsqrt0 : 0 <= Real.sqrt (n : Real) := Real.sqrt_nonneg _
  have hc1u0 : 0 <= c1 * fp.u := mul_nonneg hc1 fp.u_nonneg
  have hc3u0 : 0 <= c3 * fp.u := mul_nonneg hc3 fp.u_nonneg
  have hetaE0 : 0 <= etaE := by
    dsimp [etaE]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hsqrt0 hc1) fp.u_nonneg) hnormA0
  have hetaD0 : 0 <= etaD := by
    dsimp [etaD]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hsqrt0 hc3) fp.u_nonneg) hnormA0
  have hAop : rectOpNorm2Le A normA := by
    dsimp [normA]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl
  have hAplusOp : rectOpNorm2Le Aplus rhoA := by
    dsimp [rhoA]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le Aplus le_rfl
  have hAfrob : frobNormRect A <= Real.sqrt (n : Real) * normA :=
    frobNormRect_le_sqrt_card_mul_of_rectOpNorm2Le A hnormA0 hAop
  have hexact := higham19_13_literal_mgs_padded_exact_closed
    fp A hnm hm hpivot
  obtain ⟨Qrepair, dA2, hQrepair, hrepair, hrepairCol0⟩ :=
    hexact.eq19_31_repaired_factorization
  have hEid : (fun i j => A i j + E i j) =
      matMulRect m n n Qhat Rhat := by
    ext i j
    simpa [E, Qhat, Rhat] using hexact.eq19_29_product_identity i j
  have hEbound0 : frobNormRect E <=
      mgsProductGlobalCoeff fp m n * frobNormRect A := by
    simpa [E, Qhat, Rhat] using hexact.eq19_29_product_frob_bound
  have hproduct0 : 0 <= mgsProductGlobalCoeff fp m n :=
    mgsProductGlobalCoeff_nonneg fp m n hm
  have hEbound : frobNormRect E <= etaE := by
    calc
      frobNormRect E <=
          mgsProductGlobalCoeff fp m n * frobNormRect A := hEbound0
      _ <= (c1 * fp.u) * frobNormRect A :=
        mul_le_mul_of_nonneg_right hproductCoeff (frobNormRect_nonneg A)
      _ <= (c1 * fp.u) * (Real.sqrt (n : Real) * normA) :=
        mul_le_mul_of_nonneg_left hAfrob hc1u0
      _ = etaE := by simp [etaE]; ring
  have hEop : rectOpNorm2Le E etaE :=
    rectOpNorm2Le_of_frobNormRect_le E hEbound
  have hrepairCol : forall j : Fin n,
      columnFrob dA2 j <= c3 * fp.u * columnFrob A j := by
    intro j
    exact hrepairCol0 j |>.trans
      (mul_le_mul_of_nonneg_right hrepairCoeff (columnFrob_nonneg A j))
  have hdA2frob0 : frobNormRect dA2 <=
      (c3 * fp.u) * frobNormRect A := by
    apply frobNormRect_le_of_col_vecNorm2_le dA2 A hc3u0
    intro j
    simpa [columnFrob_eq_vecNorm2] using hrepairCol j
  have hdA2bound : frobNormRect dA2 <= etaD := by
    calc
      frobNormRect dA2 <= (c3 * fp.u) * frobNormRect A := hdA2frob0
      _ <= (c3 * fp.u) * (Real.sqrt (n : Real) * normA) :=
        mul_le_mul_of_nonneg_left hAfrob hc3u0
      _ = etaD := by simp [etaD]; ring
  have hdA2op : rectOpNorm2Le dA2 etaD :=
    rectOpNorm2Le_of_frobNormRect_le dA2 hdA2bound
  have hdet : Matrix.det (Rhat : Matrix (Fin n) (Fin n) Real) ≠ 0 := by
    apply det_ne_zero_of_upper_triangular_diag_ne_zero n Rhat
    · intro i j hji
      exact hexact.upper i j hji
    · intro i
      simpa [Rhat] using hpivot i
  have hRright : rectMatMul Rhat Rinv = idMatrix n := by
    ext i j
    exact (isInverse_nonsingInv_of_det_ne_zero n Rhat hdet).2 i j
  have hrhoEta : rhoA * etaD =
      Real.sqrt (n : Real) * c3 * fp.u * kappaA := by
    simp [etaD, kappaA, mgsSourceKappa2With, normA, rhoA]
    ring
  have hsmall' : rhoA * etaD < 1 := by
    rw [hrhoEta]
    simpa [kappaA] using hsmall
  have hRinvOp : rectOpNorm2Le Rinv (rhoA / (1 - rhoA * etaD)) :=
    repaired_qr_right_inverse_rectOpNorm2Le_of_source_left_inverse
      A dA2 Qrepair Aplus Rhat Rinv hleft
      (by simpa [matMulRect_eq_rectMatMul, Rhat] using hrepair)
      hRright hQrepair hrhoA0 hetaD0 hAplusOp hdA2op hsmall'
  have hclose0 : rectOpNorm2Le (fun i k => Qhat i k - Qrepair i k)
      ((etaE + etaD) * (rhoA / (1 - rhoA * etaD))) := by
    apply commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
      hEid hrepair
    · simpa [matMulRect_eq_rectMatMul] using hRright
    · exact hEop
    · exact hdA2op
    · exact hRinvOp
    · exact add_nonneg hetaE0 hetaD0
  have hden : 0 < 1 - rhoA * etaD := by linarith
  have hradius :
      ((etaE + etaD) * (rhoA / (1 - rhoA * etaD))) =
        mgsSourceOrthogonalityRadius fp A Aplus c1 c3 := by
    simp [etaE, etaD, rhoA, normA, kappaA,
      mgsSourceOrthogonalityRadius, mgsSourceKappa2With]
    field_simp
  have hclose : rectOpNorm2Le (fun i k => Qhat i k - Qrepair i k)
      (mgsSourceOrthogonalityRadius fp A Aplus c1 c3) := by
    rw [← hradius]
    exact hclose0
  have hradius0 : 0 <= mgsSourceOrthogonalityRadius fp A Aplus c1 c3 := by
    rw [← hradius]
    exact mul_nonneg (add_nonneg hetaE0 hetaD0)
      (div_nonneg hrhoA0 (le_of_lt hden))
  have horth : opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (2 * mgsSourceOrthogonalityRadius fp A Aplus c1 c3 +
        (mgsSourceOrthogonalityRadius fp A Aplus c1 c3) ^ 2) :=
    gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
      hQrepair hclose hradius0
  refine
    { upper := by simpa [Rhat] using hexact.upper
      eq19_29_product_identity := ?_
      eq19_29_product_op2_bound := ?_
      eq19_30_orthogonality := ?_
      eq19_31_repaired_factorization := ?_ }
  · intro i j
    simpa [E, Qhat, Rhat] using hexact.eq19_29_product_identity i j
  · simpa [E, Qhat, Rhat, etaE, normA] using hEop
  · simpa [Qhat] using horth
  · exact ⟨Qrepair, dA2, hQrepair, hrepair, hrepairCol⟩

/-- Canonical full-column-rank spectral condition number used by the final
Theorem 19.13 wrapper. -/
def mgsSourceKappa2 {m n : Nat} (A : Fin m -> Fin n -> Real) : Real :=
  mgsSourceKappa2With A (lsAplusOfGramNonsingInv A)

theorem mgsSourceKappa2_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) : 0 <= mgsSourceKappa2 A :=
  mgsSourceKappa2With_nonneg A (lsAplusOfGramNonsingInv A)

/-- Full-column-rank specialization using the canonical Moore--Penrose
inverse `(A^T A)^{-1}A^T`. -/
theorem higham19_13_literal_mgs_source_rate_canonical_of_coefficient_bounds
    {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real) (c1 c3 : Real)
    (hnm : n <= m)
    (hfull : Function.Injective (rectMatMulVec A))
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hc1 : 0 <= c1) (hc3 : 0 <= c3)
    (hproductCoeff : mgsProductGlobalCoeff fp m n <= c1 * fp.u)
    (hrepairCoeff :
      2 * mgsPaddedAccumulatedCoeff fp m n <= c3 * fp.u)
    (hsmall :
      Real.sqrt (n : Real) * c3 * fp.u * mgsSourceKappa2 A < 1) :
    LiteralMGSTheorem1913SourceRateCertificate m n fp A
      (lsAplusOfGramNonsingInv A) c1 c3 := by
  have hleft : rectMatMul (lsAplusOfGramNonsingInv A) A = idMatrix n :=
    (lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric
      A hfull).1
  apply higham19_13_literal_mgs_source_rate_of_coefficient_bounds
    fp A (lsAplusOfGramNonsingInv A) c1 c3 hnm hm hpivot hleft
    hc1 hc3 hproductCoeff hrepairCoeff
  simpa [mgsSourceKappa2] using hsmall

/-! ## Dimension-only coefficient compression -/

def mgsSourceGammaCoeff (m : Nat) : Real := 2 * ((m + 1 : Nat) : Real)

def mgsSourceNormalizationCoeff (m : Nat) : Real :=
  2 * (mgsSourceGammaCoeff m + 1)

def mgsSourceQCap (m : Nat) : Real :=
  1 + mgsSourceNormalizationCoeff m

def mgsSourceUpdateCoeff (m : Nat) : Real :=
  1 + (4 * mgsSourceGammaCoeff m + 3) * (mgsSourceQCap m) ^ 2

def mgsSourceBottomCoeff (m : Nat) : Real :=
  mgsSourceUpdateCoeff m +
    mgsSourceNormalizationCoeff m * (2 + mgsSourceNormalizationCoeff m)

def mgsSourceTopCoeff (m : Nat) : Real :=
  mgsSourceGammaCoeff m * mgsSourceQCap m +
    mgsSourceNormalizationCoeff m

def mgsSourceStepCoeff (m : Nat) : Real :=
  mgsSourceGammaCoeff m + mgsSourceTopCoeff m + mgsSourceBottomCoeff m

def mgsSourceStageGrowthCap (m : Nat) : Real :=
  2 + mgsSourceBottomCoeff m

def mgsSourceReconstructionCoeff (m : Nat) : Real :=
  mgsSourceUpdateCoeff m +
    mgsSourceGammaCoeff m * (mgsSourceQCap m) ^ 2

def mgsSourceProductColumnCoeff (m j : Nat) : Real :=
  (mgsSourceStageGrowthCap m) ^ j +
    Finset.univ.sum (fun k : Fin j =>
      mgsSourceReconstructionCoeff m *
        (mgsSourceStageGrowthCap m) ^ k.val)

def mgsSourceProductGlobalCoeff (m n : Nat) : Real :=
  Finset.univ.sum (fun j : Fin n =>
    mgsSourceProductColumnCoeff m j.val)

def mgsSourceRepairCoeff (m n : Nat) : Real :=
  2 * ((n : Nat) : Real) * mgsSourceStepCoeff m *
    (1 + mgsSourceStepCoeff m) ^ n

theorem mgsSourceGammaCoeff_nonneg (m : Nat) :
    0 <= mgsSourceGammaCoeff m := by
  unfold mgsSourceGammaCoeff
  exact mul_nonneg (by norm_num) (by positivity)

theorem mgsSourceNormalizationCoeff_nonneg (m : Nat) :
    0 <= mgsSourceNormalizationCoeff m := by
  unfold mgsSourceNormalizationCoeff
  exact mul_nonneg (by norm_num)
    (add_nonneg (mgsSourceGammaCoeff_nonneg m) (by norm_num))

theorem mgsSourceQCap_nonneg (m : Nat) : 0 <= mgsSourceQCap m := by
  unfold mgsSourceQCap
  exact add_nonneg (by norm_num) (mgsSourceNormalizationCoeff_nonneg m)

theorem mgsSourceUpdateCoeff_nonneg (m : Nat) :
    0 <= mgsSourceUpdateCoeff m := by
  unfold mgsSourceUpdateCoeff
  exact add_nonneg (by norm_num)
    (mul_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (mgsSourceGammaCoeff_nonneg m))
        (by norm_num))
      (sq_nonneg _))

theorem mgsSourceBottomCoeff_nonneg (m : Nat) :
    0 <= mgsSourceBottomCoeff m := by
  unfold mgsSourceBottomCoeff
  exact add_nonneg (mgsSourceUpdateCoeff_nonneg m)
    (mul_nonneg (mgsSourceNormalizationCoeff_nonneg m)
      (add_nonneg (by norm_num) (mgsSourceNormalizationCoeff_nonneg m)))

theorem mgsSourceTopCoeff_nonneg (m : Nat) :
    0 <= mgsSourceTopCoeff m := by
  unfold mgsSourceTopCoeff
  exact add_nonneg
    (mul_nonneg (mgsSourceGammaCoeff_nonneg m) (mgsSourceQCap_nonneg m))
    (mgsSourceNormalizationCoeff_nonneg m)

theorem mgsSourceStepCoeff_nonneg (m : Nat) :
    0 <= mgsSourceStepCoeff m := by
  unfold mgsSourceStepCoeff
  exact add_nonneg
    (add_nonneg (mgsSourceGammaCoeff_nonneg m) (mgsSourceTopCoeff_nonneg m))
    (mgsSourceBottomCoeff_nonneg m)

theorem mgsSourceStageGrowthCap_nonneg (m : Nat) :
    0 <= mgsSourceStageGrowthCap m := by
  unfold mgsSourceStageGrowthCap
  exact add_nonneg (by norm_num) (mgsSourceBottomCoeff_nonneg m)

theorem mgsSourceReconstructionCoeff_nonneg (m : Nat) :
    0 <= mgsSourceReconstructionCoeff m := by
  unfold mgsSourceReconstructionCoeff
  exact add_nonneg (mgsSourceUpdateCoeff_nonneg m)
    (mul_nonneg (mgsSourceGammaCoeff_nonneg m) (sq_nonneg _))

theorem mgsSourceProductColumnCoeff_nonneg (m j : Nat) :
    0 <= mgsSourceProductColumnCoeff m j := by
  unfold mgsSourceProductColumnCoeff
  exact add_nonneg (pow_nonneg (mgsSourceStageGrowthCap_nonneg m) _)
    (Finset.sum_nonneg fun k _ =>
      mul_nonneg (mgsSourceReconstructionCoeff_nonneg m)
        (pow_nonneg (mgsSourceStageGrowthCap_nonneg m) _))

theorem mgsSourceProductGlobalCoeff_nonneg (m n : Nat) :
    0 <= mgsSourceProductGlobalCoeff m n := by
  unfold mgsSourceProductGlobalCoeff
  exact Finset.sum_nonneg fun j _ =>
    mgsSourceProductColumnCoeff_nonneg m j.val

theorem mgsSourceRepairCoeff_nonneg (m n : Nat) :
    0 <= mgsSourceRepairCoeff m n := by
  unfold mgsSourceRepairCoeff
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (mgsSourceStepCoeff_nonneg m))
    (pow_nonneg
      (add_nonneg (by norm_num) (mgsSourceStepCoeff_nonneg m)) _)

theorem mgsSource_u_lt_one (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1))) : fp.u < 1 := by
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hm
  simpa [gammaValid] using h1

theorem mgsSource_gamma_le (fp : FPModel) (m : Nat)
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    gamma fp (m + 1) <= mgsSourceGammaCoeff m * fp.u := by
  have hsmall' : (((m + 1 : Nat) : Real) * fp.u <= 1 / 2) := by
    calc
      ((m + 1 : Nat) : Real) * fp.u <=
          ((2 * (m + 1) : Nat) : Real) * fp.u := by
        apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
        push_cast
        have hm0 : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
        linarith
      _ <= 1 / 2 := hsmall
  have h := gamma_le_two_mul_n_u_of_nu_le_half fp (m + 1) hsmall'
  convert h using 1 <;> simp [mgsSourceGammaCoeff] <;> ring

theorem mgsSource_gamma_m_le (fp : FPModel) (m : Nat)
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    gamma fp m <= mgsSourceGammaCoeff m * fp.u := by
  have hsmall' : (m : Real) * fp.u <= 1 / 2 := by
    calc
      (m : Real) * fp.u <= ((2 * (m + 1) : Nat) : Real) * fp.u := by
        apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
        push_cast
        have hm0 : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
        linarith
      _ <= 1 / 2 := hsmall
  have h := gamma_le_two_mul_n_u_of_nu_le_half fp m hsmall'
  calc
    gamma fp m <= 2 * ((m : Real) * fp.u) := h
    _ <= mgsSourceGammaCoeff m * fp.u := by
      unfold mgsSourceGammaCoeff
      push_cast
      nlinarith [fp.u_nonneg]

theorem mgsNormalizationEps_le_sourceCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsNormalizationEps fp m <= mgsSourceNormalizationCoeff m * fp.u := by
  let G := mgsSourceGammaCoeff m
  have hG0 : 0 <= G := mgsSourceGammaCoeff_nonneg m
  have hg := mgsSource_gamma_le fp m hsmall
  have hGu : G * fp.u <= 1 / 2 := by
    simpa [G, mgsSourceGammaCoeff] using hsmall
  have hgHalf : gamma fp (m + 1) <= 1 / 2 := hg.trans hGu
  have hdenHalf : 1 / 2 <= 1 - gamma fp (m + 1) := by linarith
  have hdenPos : 0 < 1 - gamma fp (m + 1) := by linarith
  have hnum : gamma fp (m + 1) + fp.u <= (G + 1) * fp.u := by
    dsimp [G] at hg ⊢
    linarith
  have hscale0 : 0 <= 2 * (G + 1) * fp.u := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg hG0 (by norm_num))) fp.u_nonneg
  have hscale : (G + 1) * fp.u <=
      (2 * (G + 1) * fp.u) * (1 - gamma fp (m + 1)) := by
    have h := mul_le_mul_of_nonneg_left hdenHalf hscale0
    nlinarith
  unfold mgsNormalizationEps mgsSourceNormalizationCoeff
  apply (div_le_iff₀ hdenPos).2
  dsimp [G] at hnum hscale ⊢
  exact hnum.trans hscale

theorem mgsComputedQNormCap_le_sourceQCap
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsComputedQNormCap fp m <= mgsSourceQCap m := by
  have heps := mgsNormalizationEps_le_sourceCoeff_mul_u fp m hm hsmall
  have hu : fp.u <= 1 := le_of_lt (mgsSource_u_lt_one fp m hm)
  have hEcoeff := mgsSourceNormalizationCoeff_nonneg m
  have heu : mgsSourceNormalizationCoeff m * fp.u <=
      mgsSourceNormalizationCoeff m := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu hEcoeff
  unfold mgsComputedQNormCap mgsSourceQCap
  linarith

theorem mgsUpdateLocalNormCap_le_sourceUpdateCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsUpdateLocalNormCap fp m <= mgsSourceUpdateCoeff m * fp.u := by
  let G := mgsSourceGammaCoeff m
  let Q := mgsSourceQCap m
  let K : Real :=
    (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u
  have hG0 : 0 <= G := mgsSourceGammaCoeff_nonneg m
  have hQ0 : 0 <= Q := mgsSourceQCap_nonneg m
  have hu1 : fp.u <= 1 := le_of_lt (mgsSource_u_lt_one fp m hm)
  have h1u0 : 0 <= 1 + fp.u := add_nonneg (by norm_num) fp.u_nonneg
  have h1u2 : 1 + fp.u <= 2 := by linarith
  have hm0 : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hg0 : 0 <= gamma fp m := gamma_nonneg fp hm0
  have hg : gamma fp m <= G * fp.u := by
    simpa [G] using mgsSource_gamma_m_le fp m hsmall
  have hGu0 : 0 <= G * fp.u := mul_nonneg hG0 fp.u_nonneg
  have hfirst0 : 0 <= gamma fp m * (1 + fp.u) + fp.u :=
    add_nonneg (mul_nonneg hg0 h1u0) fp.u_nonneg
  have hfirst : gamma fp m * (1 + fp.u) + fp.u <=
      (2 * G + 1) * fp.u := by
    calc
      gamma fp m * (1 + fp.u) + fp.u <=
          (G * fp.u) * (1 + fp.u) + fp.u :=
        by
          simpa [add_comm] using
            (add_le_add_right (mul_le_mul_of_nonneg_right hg h1u0) fp.u)
      _ <= (G * fp.u) * 2 + fp.u :=
        by
          simpa [add_comm] using
            (add_le_add_right (mul_le_mul_of_nonneg_left h1u2 hGu0) fp.u)
      _ = (2 * G + 1) * fp.u := by ring
  have hcoeff1u0 : 0 <= (2 * G + 1) * fp.u := by
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hG0) (by norm_num)) fp.u_nonneg
  have hsecond :
      (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) <=
        ((2 * G + 1) * fp.u) * 2 := by
    calc
      (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) <=
          ((2 * G + 1) * fp.u) * (1 + fp.u) :=
        mul_le_mul_of_nonneg_right hfirst h1u0
      _ <= ((2 * G + 1) * fp.u) * 2 :=
        mul_le_mul_of_nonneg_left h1u2 hcoeff1u0
  have hK : K <= (4 * G + 3) * fp.u := by
    dsimp [K]
    calc
      (gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u <=
          ((2 * G + 1) * fp.u) * 2 + fp.u :=
        by simpa [add_comm] using (add_le_add_right hsecond fp.u)
      _ = (4 * G + 3) * fp.u := by ring
  have hK0 : 0 <= K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hfirst0 h1u0) fp.u_nonneg
  have hKcoeff0 : 0 <= 4 * G + 3 :=
    add_nonneg (mul_nonneg (by norm_num) hG0) (by norm_num)
  have hKcoeffu0 : 0 <= (4 * G + 3) * fp.u :=
    mul_nonneg hKcoeff0 fp.u_nonneg
  have hq := mgsComputedQNormCap_le_sourceQCap fp m hm hsmall
  have heps0 := mgsNormalizationEps_nonneg fp m hm
  have hq0 : 0 <= mgsComputedQNormCap fp m := by
    unfold mgsComputedQNormCap
    linarith
  have hqSq : (mgsComputedQNormCap fp m) ^ 2 <= Q ^ 2 := by
    nlinarith [sq_nonneg (Q - mgsComputedQNormCap fp m)]
  have hprod : K * (mgsComputedQNormCap fp m) ^ 2 <=
      ((4 * G + 3) * fp.u) * Q ^ 2 := by
    calc
      K * (mgsComputedQNormCap fp m) ^ 2 <=
          ((4 * G + 3) * fp.u) * (mgsComputedQNormCap fp m) ^ 2 :=
        mul_le_mul_of_nonneg_right hK (sq_nonneg _)
      _ <= ((4 * G + 3) * fp.u) * Q ^ 2 :=
        mul_le_mul_of_nonneg_left hqSq hKcoeffu0
  unfold mgsUpdateLocalNormCap mgsSourceUpdateCoeff
  dsimp [K] at hprod
  dsimp [G, Q] at hprod ⊢
  calc
    fp.u +
        (((gamma fp m * (1 + fp.u) + fp.u) * (1 + fp.u) + fp.u) *
          mgsComputedQNormCap fp m ^ 2) <=
      fp.u +
        (((4 * mgsSourceGammaCoeff m + 3) * fp.u) *
          mgsSourceQCap m ^ 2) := by
      simpa [add_comm] using (add_le_add_left hprod fp.u)
    _ = (1 + (4 * mgsSourceGammaCoeff m + 3) *
          mgsSourceQCap m ^ 2) * fp.u := by ring

theorem mgsPaddedBottomStepCoeff_le_sourceBottomCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsPaddedBottomStepCoeff fp m <= mgsSourceBottomCoeff m * fp.u := by
  let E := mgsSourceNormalizationCoeff m
  have hE0 : 0 <= E := mgsSourceNormalizationCoeff_nonneg m
  have hu1 : fp.u <= 1 := le_of_lt (mgsSource_u_lt_one fp m hm)
  have heps := mgsNormalizationEps_le_sourceCoeff_mul_u fp m hm hsmall
  have heps0 := mgsNormalizationEps_nonneg fp m hm
  have hEu0 : 0 <= E * fp.u := mul_nonneg hE0 fp.u_nonneg
  have hEuE : E * fp.u <= E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hE0
  have hepsE : mgsNormalizationEps fp m <= E := heps.trans hEuE
  have htwoeps0 : 0 <= 2 + mgsNormalizationEps fp m := by linarith
  have htwoeps : 2 + mgsNormalizationEps fp m <= 2 + E := by linarith
  have htail : mgsNormalizationEps fp m *
      (2 + mgsNormalizationEps fp m) <= (E * fp.u) * (2 + E) := by
    calc
      mgsNormalizationEps fp m * (2 + mgsNormalizationEps fp m) <=
          (E * fp.u) * (2 + mgsNormalizationEps fp m) :=
        mul_le_mul_of_nonneg_right heps htwoeps0
      _ <= (E * fp.u) * (2 + E) :=
        mul_le_mul_of_nonneg_left htwoeps hEu0
  have hupdate := mgsUpdateLocalNormCap_le_sourceUpdateCoeff_mul_u
    fp m hm hsmall
  unfold mgsPaddedBottomStepCoeff mgsSourceBottomCoeff
  dsimp [E] at htail
  calc
    mgsUpdateLocalNormCap fp m +
        mgsNormalizationEps fp m * (2 + mgsNormalizationEps fp m) <=
      mgsSourceUpdateCoeff m * fp.u +
        (mgsSourceNormalizationCoeff m * fp.u) *
          (2 + mgsSourceNormalizationCoeff m) := add_le_add hupdate htail
    _ = (mgsSourceUpdateCoeff m +
        mgsSourceNormalizationCoeff m *
          (2 + mgsSourceNormalizationCoeff m)) * fp.u := by ring

theorem mgsPaddedTopStepCoeff_le_sourceTopCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsPaddedTopStepCoeff fp m <= mgsSourceTopCoeff m * fp.u := by
  let G := mgsSourceGammaCoeff m
  let Q := mgsSourceQCap m
  let E := mgsSourceNormalizationCoeff m
  have hG0 : 0 <= G := mgsSourceGammaCoeff_nonneg m
  have hQ0 : 0 <= Q := mgsSourceQCap_nonneg m
  have hg0 : 0 <= gamma fp m :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hm)
  have hg : gamma fp m <= G * fp.u := by
    simpa [G] using mgsSource_gamma_m_le fp m hsmall
  have hq := mgsComputedQNormCap_le_sourceQCap fp m hm hsmall
  have hq0 : 0 <= mgsComputedQNormCap fp m := by
    unfold mgsComputedQNormCap
    exact add_nonneg (by norm_num) (mgsNormalizationEps_nonneg fp m hm)
  have hprod : gamma fp m * mgsComputedQNormCap fp m <=
      (G * fp.u) * Q := by
    calc
      gamma fp m * mgsComputedQNormCap fp m <=
          (G * fp.u) * mgsComputedQNormCap fp m :=
        mul_le_mul_of_nonneg_right hg hq0
      _ <= (G * fp.u) * Q :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hG0 fp.u_nonneg)
  have heps := mgsNormalizationEps_le_sourceCoeff_mul_u fp m hm hsmall
  unfold mgsPaddedTopStepCoeff mgsSourceTopCoeff
  dsimp [G, Q, E] at hprod heps ⊢
  calc
    gamma fp m * mgsComputedQNormCap fp m + mgsNormalizationEps fp m <=
      (mgsSourceGammaCoeff m * fp.u) * mgsSourceQCap m +
        mgsSourceNormalizationCoeff m * fp.u := add_le_add hprod heps
    _ = (mgsSourceGammaCoeff m * mgsSourceQCap m +
        mgsSourceNormalizationCoeff m) * fp.u := by ring

theorem mgsPaddedStepCoeff_le_sourceStepCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsPaddedStepCoeff fp m <= mgsSourceStepCoeff m * fp.u := by
  have hg := mgsSource_gamma_le fp m hsmall
  have ht := mgsPaddedTopStepCoeff_le_sourceTopCoeff_mul_u fp m hm hsmall
  have hb := mgsPaddedBottomStepCoeff_le_sourceBottomCoeff_mul_u fp m hm hsmall
  unfold mgsPaddedStepCoeff mgsSourceStepCoeff
  calc
    gamma fp (m + 1) + mgsPaddedTopStepCoeff fp m +
        mgsPaddedBottomStepCoeff fp m <=
      mgsSourceGammaCoeff m * fp.u +
        mgsSourceTopCoeff m * fp.u + mgsSourceBottomCoeff m * fp.u :=
      add_le_add (add_le_add hg ht) hb
    _ = (mgsSourceGammaCoeff m + mgsSourceTopCoeff m +
        mgsSourceBottomCoeff m) * fp.u := by ring

theorem mgsStageGrowthCoeff_le_sourceStageGrowthCap
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsStageGrowthCoeff fp m <= mgsSourceStageGrowthCap m := by
  have hb := mgsPaddedBottomStepCoeff_le_sourceBottomCoeff_mul_u
    fp m hm hsmall
  have hu1 : fp.u <= 1 := le_of_lt (mgsSource_u_lt_one fp m hm)
  have hB0 : 0 <= mgsSourceBottomCoeff m :=
    mgsSourceBottomCoeff_nonneg m
  have hBu : mgsSourceBottomCoeff m * fp.u <=
      mgsSourceBottomCoeff m := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hB0
  unfold mgsStageGrowthCoeff mgsSourceStageGrowthCap
  linarith

theorem mgsReconstructionStepCoeff_le_sourceReconstructionCoeff_mul_u
    (fp : FPModel) (m : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsReconstructionStepCoeff fp m <=
      mgsSourceReconstructionCoeff m * fp.u := by
  let G := mgsSourceGammaCoeff m
  let Q := mgsSourceQCap m
  have hG0 : 0 <= G := mgsSourceGammaCoeff_nonneg m
  have hq := mgsComputedQNormCap_le_sourceQCap fp m hm hsmall
  have hq0 : 0 <= mgsComputedQNormCap fp m := by
    unfold mgsComputedQNormCap
    exact add_nonneg (by norm_num) (mgsNormalizationEps_nonneg fp m hm)
  have hqSq : (mgsComputedQNormCap fp m) ^ 2 <= Q ^ 2 := by
    nlinarith [sq_nonneg (Q - mgsComputedQNormCap fp m)]
  have hg0 : 0 <= gamma fp m :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hm)
  have hg : gamma fp m <= G * fp.u := by
    simpa [G] using mgsSource_gamma_m_le fp m hsmall
  have hgammaProd :
      gamma fp m * (mgsComputedQNormCap fp m) ^ 2 <=
        (G * fp.u) * Q ^ 2 := by
    calc
      gamma fp m * (mgsComputedQNormCap fp m) ^ 2 <=
          (G * fp.u) * (mgsComputedQNormCap fp m) ^ 2 :=
        mul_le_mul_of_nonneg_right hg (sq_nonneg _)
      _ <= (G * fp.u) * Q ^ 2 :=
        mul_le_mul_of_nonneg_left hqSq (mul_nonneg hG0 fp.u_nonneg)
  have hu := mgsUpdateLocalNormCap_le_sourceUpdateCoeff_mul_u
    fp m hm hsmall
  unfold mgsReconstructionStepCoeff mgsSourceReconstructionCoeff
  dsimp [G, Q] at hgammaProd ⊢
  calc
    mgsUpdateLocalNormCap fp m +
        gamma fp m * mgsComputedQNormCap fp m ^ 2 <=
      mgsSourceUpdateCoeff m * fp.u +
        (mgsSourceGammaCoeff m * fp.u) * mgsSourceQCap m ^ 2 :=
      add_le_add hu hgammaProd
    _ = (mgsSourceUpdateCoeff m +
        mgsSourceGammaCoeff m * mgsSourceQCap m ^ 2) * fp.u := by ring

theorem mgsPaddedAccumulatedCoeff_le_sourceRepairCoeff_mul_u
    (fp : FPModel) (m n : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    2 * mgsPaddedAccumulatedCoeff fp m n <=
      mgsSourceRepairCoeff m n * fp.u := by
  let s := mgsPaddedStepCoeff fp m
  let S := mgsSourceStepCoeff m
  have hs0 : 0 <= s := mgsPaddedStepCoeff_nonneg fp m hm
  have hS0 : 0 <= S := mgsSourceStepCoeff_nonneg m
  have hsu : s <= S * fp.u := by
    simpa [s, S] using mgsPaddedStepCoeff_le_sourceStepCoeff_mul_u
      fp m hm hsmall
  have hu1 : fp.u <= 1 := le_of_lt (mgsSource_u_lt_one fp m hm)
  have hSuS : S * fp.u <= S := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hS0
  have hsS : s <= S := hsu.trans hSuS
  have hbase0 : 0 <= 1 + s := by linarith
  have hbasePow : (1 + s) ^ n <= (1 + S) ^ n :=
    pow_le_pow_left₀ hbase0 (by linarith) n
  have hpow0 : 0 <= (1 + s) ^ n := pow_nonneg hbase0 n
  have hSPow0 : 0 <= (1 + S) ^ n :=
    pow_nonneg (by linarith : 0 <= 1 + S) n
  have hacc := one_add_pow_sub_one_le_nat_mul_growth hs0 n
  have hcoef : (n : Real) * s <= (n : Real) * (S * fp.u) :=
    mul_le_mul_of_nonneg_left hsu (Nat.cast_nonneg n)
  have hprod : (n : Real) * s * (1 + s) ^ n <=
      ((n : Real) * (S * fp.u)) * (1 + S) ^ n := by
    calc
      (n : Real) * s * (1 + s) ^ n <=
          ((n : Real) * (S * fp.u)) * (1 + s) ^ n :=
        mul_le_mul_of_nonneg_right hcoef hpow0
      _ <= ((n : Real) * (S * fp.u)) * (1 + S) ^ n :=
        mul_le_mul_of_nonneg_left hbasePow
          (mul_nonneg (Nat.cast_nonneg n)
            (mul_nonneg hS0 fp.u_nonneg))
  unfold mgsPaddedAccumulatedCoeff mgsSourceRepairCoeff
  dsimp [s, S] at hacc hprod ⊢
  calc
    2 * ((1 + mgsPaddedStepCoeff fp m) ^ n - 1) <=
        2 * ((n : Real) * mgsPaddedStepCoeff fp m *
          (1 + mgsPaddedStepCoeff fp m) ^ n) :=
      mul_le_mul_of_nonneg_left hacc (by norm_num)
    _ <= 2 * (((n : Real) *
        (mgsSourceStepCoeff m * fp.u)) *
          (1 + mgsSourceStepCoeff m) ^ n) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (2 * (n : Real) * mgsSourceStepCoeff m *
        (1 + mgsSourceStepCoeff m) ^ n) * fp.u := by ring

theorem mgsProductColumnCoeff_le_sourceProductColumnCoeff_mul_u
    (fp : FPModel) (m j : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsProductColumnCoeff fp m j <=
      mgsSourceProductColumnCoeff m j * fp.u := by
  have hg := mgsStageGrowthCoeff_le_sourceStageGrowthCap fp m hm hsmall
  have hg0 := mgsStageGrowthCoeff_nonneg fp m hm
  have hr :=
    mgsReconstructionStepCoeff_le_sourceReconstructionCoeff_mul_u
      fp m hm hsmall
  have hr0 := mgsReconstructionStepCoeff_nonneg fp m hm
  have hpow : forall k : Nat,
      (mgsStageGrowthCoeff fp m) ^ k <=
        (mgsSourceStageGrowthCap m) ^ k := fun k =>
    pow_le_pow_left₀ hg0 hg k
  unfold mgsProductColumnCoeff mgsSourceProductColumnCoeff
  calc
    fp.u * mgsStageGrowthCoeff fp m ^ j +
        Finset.univ.sum (fun k : Fin j =>
          mgsReconstructionStepCoeff fp m *
            mgsStageGrowthCoeff fp m ^ k.val) <=
      fp.u * mgsSourceStageGrowthCap m ^ j +
        Finset.univ.sum (fun k : Fin j =>
          (mgsSourceReconstructionCoeff m * fp.u) *
            mgsSourceStageGrowthCap m ^ k.val) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hpow j) fp.u_nonneg
      · apply Finset.sum_le_sum
        intro k _
        calc
          mgsReconstructionStepCoeff fp m *
              mgsStageGrowthCoeff fp m ^ k.val <=
            (mgsSourceReconstructionCoeff m * fp.u) *
              mgsStageGrowthCoeff fp m ^ k.val :=
            mul_le_mul_of_nonneg_right hr (pow_nonneg hg0 _)
          _ <= (mgsSourceReconstructionCoeff m * fp.u) *
              mgsSourceStageGrowthCap m ^ k.val :=
            mul_le_mul_of_nonneg_left (hpow k.val)
              (mul_nonneg (mgsSourceReconstructionCoeff_nonneg m)
                fp.u_nonneg)
    _ = (mgsSourceStageGrowthCap m ^ j +
        Finset.univ.sum (fun k : Fin j =>
          mgsSourceReconstructionCoeff m *
            mgsSourceStageGrowthCap m ^ k.val)) * fp.u := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro k _
        ring

theorem mgsProductGlobalCoeff_le_sourceProductGlobalCoeff_mul_u
    (fp : FPModel) (m n : Nat)
    (hm : gammaValid fp (2 * (m + 1)))
    (hsmall : (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2)) :
    mgsProductGlobalCoeff fp m n <=
      mgsSourceProductGlobalCoeff m n * fp.u := by
  unfold mgsProductGlobalCoeff mgsSourceProductGlobalCoeff
  calc
    Finset.univ.sum (fun j : Fin n =>
        mgsProductColumnCoeff fp m j.val) <=
      Finset.univ.sum (fun j : Fin n =>
        mgsSourceProductColumnCoeff m j.val * fp.u) :=
      Finset.sum_le_sum fun j _ =>
        mgsProductColumnCoeff_le_sourceProductColumnCoeff_mul_u
          fp m j.val hm hsmall
    _ = (Finset.univ.sum (fun j : Fin n =>
        mgsSourceProductColumnCoeff m j.val)) * fp.u := by
      rw [Finset.sum_mul]

/-- Premise-free coefficient specialization of the literal Theorem 19.13
source-rate package.  The remaining hypotheses are exactly the mathematical
full-rank/nonbreakdown and first-order smallness assumptions used by the
printed theorem. -/
theorem higham19_13_literal_mgs_source_rate_canonical_closed
    {m n : Nat}
    (fp : FPModel) (A : Fin m -> Fin n -> Real)
    (hnm : n <= m)
    (hfull : Function.Injective (rectMatMulVec A))
    (hm : gammaValid fp (2 * (m + 1)))
    (hpivot : forall k : Fin n,
      Ne (fl_modifiedGramSchmidtR fp A k k) 0)
    (hmodelSmall :
      (((2 * (m + 1) : Nat) : Real) * fp.u <= 1 / 2))
    (hconditionSmall :
      Real.sqrt (n : Real) * mgsSourceRepairCoeff m n * fp.u *
          mgsSourceKappa2 A < 1) :
    LiteralMGSTheorem1913SourceRateCertificate m n fp A
      (lsAplusOfGramNonsingInv A)
      (mgsSourceProductGlobalCoeff m n)
      (mgsSourceRepairCoeff m n) := by
  apply higham19_13_literal_mgs_source_rate_canonical_of_coefficient_bounds
    fp A (mgsSourceProductGlobalCoeff m n)
      (mgsSourceRepairCoeff m n) hnm hfull hm hpivot
    (mgsSourceProductGlobalCoeff_nonneg m n)
    (mgsSourceRepairCoeff_nonneg m n)
    (mgsProductGlobalCoeff_le_sourceProductGlobalCoeff_mul_u
      fp m n hm hmodelSmall)
    (mgsPaddedAccumulatedCoeff_le_sourceRepairCoeff_mul_u
      fp m n hm hmodelSmall)
  exact hconditionSmall

end

end NumStability
