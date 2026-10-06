import NumStability.Algorithms.QR.Higham19Theorem5SourceClosure

/-!
# Higham Theorem 19.5: source-derived computed-`R` nonbreakdown

The concrete QR-solve theorems need the diagonal of the computed triangular
factor to be nonzero before rounded back substitution can be analysed.  The
source obtains this from Theorem 19.4: if `A + dA = Q R` and
`sqrt(n) * gamma_tilde * kappa_2(A) < 1`, then `A + dA`, hence `R`, is
nonsingular.

This file formalizes that argument without using a solve theorem or a target
backward-error statement.  A supplied source left inverse gives the general
form; the canonical wrappers use `(A^T A)^{-1} A^T`, constructed from source
injectivity.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- Spectral condition number represented by a particular source left
inverse. -/
def higham19QRSourceKappa2With {n : Nat}
    (A Aplus : Fin n -> Fin n -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A) *
    complexMatrixOp2 (realRectToCMatrix Aplus)

/-- Canonical source condition number for a nonsingular square matrix. -/
def higham19QRSourceKappa2 {n : Nat}
    (A : Fin n -> Fin n -> Real) : Real :=
  higham19QRSourceKappa2With A (lsAplusOfGramNonsingInv A)

/-- For a square source with injective action, the Gram-form left inverse used
by the rectangular least-squares development is the repository's canonical
nonsingular inverse.  This is a source-derived uniqueness bridge, not an
inverse-shaped hypothesis. -/
theorem lsAplusOfGramNonsingInv_eq_nonsingInv_of_square_injective
    {n : Nat} (A : Fin n -> Fin n -> Real)
    (hsource : Function.Injective (rectMatMulVec A)) :
    lsAplusOfGramNonsingInv A = nonsingInv n A := by
  have hleft :
      rectMatMul (lsAplusOfGramNonsingInv A) A = idMatrix n :=
    (lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric
      A hsource).1
  have hdet : Matrix.det (A : Matrix (Fin n) (Fin n) Real) ≠ 0 :=
    det_ne_zero_of_square_rectMatMulVec_injective hsource
  have hright : rectMatMul A (nonsingInv n A) = idMatrix n := by
    funext i j
    exact (isInverse_nonsingInv_of_det_ne_zero n A hdet).2 i j
  calc
    lsAplusOfGramNonsingInv A =
        rectMatMul (lsAplusOfGramNonsingInv A) (idMatrix n) :=
      (rectMatMul_id_right (lsAplusOfGramNonsingInv A)).symm
    _ = rectMatMul (lsAplusOfGramNonsingInv A)
        (rectMatMul A (nonsingInv n A)) := by rw [hright]
    _ = rectMatMul (rectMatMul (lsAplusOfGramNonsingInv A) A)
        (nonsingInv n A) :=
      (rectMatMul_assoc (lsAplusOfGramNonsingInv A) A
        (nonsingInv n A)).symm
    _ = rectMatMul (idMatrix n) (nonsingInv n A) := by rw [hleft]
    _ = nonsingInv n A := rectMatMul_id_left (nonsingInv n A)

/-- The Chapter-19 source condition number is exactly the repository's
standard square `κ₂(A) = ‖A‖₂ ‖A⁻¹‖₂` when the source action is injective.
This closes the notation bridge from the actual Gram inverse constructor to
the printed Theorem 19.5 smallness condition. -/
theorem higham19QRSourceKappa2_eq_kappa2_nonsingInv_of_injective
    {n : Nat} (A : Fin n -> Fin n -> Real)
    (hsource : Function.Injective (rectMatMulVec A)) :
    higham19QRSourceKappa2 A = kappa2 A (nonsingInv n A) := by
  have hopNorm_eq (M : Fin n -> Fin n -> Real) :
      complexMatrixOp2 (realRectToCMatrix M) = opNorm2 M := by
    apply le_antisymm
    · exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le M
        (opNorm2_nonneg M) (opNorm2Le_opNorm2 M)
    · exact opNorm2_le_of_opNorm2Le M
        (complexMatrixOp2_nonneg (realRectToCMatrix M))
        (opNorm2Le_complexMatrixOp2_realRectToCMatrix M)
  rw [higham19QRSourceKappa2, higham19QRSourceKappa2With,
    lsAplusOfGramNonsingInv_eq_nonsingInv_of_square_injective A hsource,
    hopNorm_eq A, hopNorm_eq (nonsingInv n A)]
  rfl

private theorem higham19_frobNormRect_le_sqrt_card_mul_of_rectOpNorm2Le
    {m n : Nat} (A : Fin m -> Fin n -> Real) {a : Real}
    (ha : 0 <= a) (hA : rectOpNorm2Le A a) :
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

/-- The computed Householder `R` has nonzero diagonal when the source matrix
has a left inverse and the Theorem 19.4 perturbation is smaller than the
source inverse radius.

The proof is deliberately upstream of back substitution: it uses only the
actual QR factorization certificate. -/
theorem fl_householderQR_R_diag_nonzero_of_source_left_inverse_small
    (fp : FPModel) (n : Nat)
    (A Aplus : Fin n -> Fin n -> Real)
    (hn : 0 < n)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hsmall :
      Real.sqrt (n : Real) *
          gamma fp (n * householderConstructApplyGammaIndex n) *
          higham19QRSourceKappa2With A Aplus < 1) :
    forall i : Fin n, fl_householderQR_R fp n A i i ≠ 0 := by
  let K := householderConstructApplyGammaIndex n
  let G := gamma fp (n * K)
  let Q := fl_householderQR_Q fp n A
  let R := fl_householderQR_R fp n A
  let normA := complexMatrixOp2 (realRectToCMatrix A)
  let rho := complexMatrixOp2 (realRectToCMatrix Aplus)
  let eta := G * (Real.sqrt (n : Real) * normA)
  have hQR :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp n n A (by simpa using hn) (by simpa [K] using hvalid)
  obtain ⟨dA, hR, hdAfrob0, _hdAcol⟩ := hQR.result
  have hQ : IsOrthogonal n Q := by simpa [Q] using hQR.orth
  have hG0 : 0 <= G := by
    simpa [G, K] using gamma_nonneg fp hvalid
  have hnormA0 : 0 <= normA := complexMatrixOp2_nonneg _
  have hrho0 : 0 <= rho := complexMatrixOp2_nonneg _
  have hAop : rectOpNorm2Le A normA := by
    dsimp [normA]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl
  have hAfrobRect : frobNormRect A <= Real.sqrt (n : Real) * normA :=
    higham19_frobNormRect_le_sqrt_card_mul_of_rectOpNorm2Le
      A hnormA0 hAop
  have hAfrob : frobNorm A <= Real.sqrt (n : Real) * normA := by
    simpa [frobNormRect_eq_frobNormFn] using hAfrobRect
  have hdAfrob : frobNorm dA <= eta := by
    calc
      frobNorm dA <= G * frobNorm A := by
        simpa [G, K] using hdAfrob0
      _ <= G * (Real.sqrt (n : Real) * normA) :=
        mul_le_mul_of_nonneg_left hAfrob hG0
      _ = eta := rfl
  have hdAop : rectOpNorm2Le dA eta := by
    apply rectOpNorm2Le_of_frobNormRect_le
    simpa [frobNormRect_eq_frobNormFn] using hdAfrob
  have hAplusOp : rectOpNorm2Le Aplus rho := by
    dsimp [rho]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le Aplus le_rfl
  let E : Fin n -> Fin n -> Real := rectMatMul Aplus dA
  have hEop : rectOpNorm2Le E (rho * eta) := by
    dsimp [E]
    exact rectOpNorm2Le_rectMatMul Aplus dA hrho0 hAplusOp hdAop
  have hdeltaEq :
      rho * eta =
        Real.sqrt (n : Real) * G * higham19QRSourceKappa2With A Aplus := by
    simp [rho, eta, normA, higham19QRSourceKappa2With]
    ring
  have hdelta : rho * eta < 1 := by
    rw [hdeltaEq]
    simpa [G, K] using hsmall
  have hlowerId : forall x : Fin n -> Real,
      (1 : Real) * vecNorm2 x <=
        vecNorm2 (rectMatMulVec (idMatrix n) x) := by
    intro x
    simp [rectMatMulVec_idMatrix]
  have hinjIdE : Function.Injective
      (rectMatMulVec (fun i j => idMatrix n i j + E i j)) :=
    rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
      hlowerId hEop hdelta
  let Apert : Fin n -> Fin n -> Real := fun i j => A i j + dA i j
  have hMrep :
      rectMatMul Aplus Apert =
        (fun i j => idMatrix n i j + E i j) := by
    dsimp [Apert, E]
    rw [rectMatMul_add_right, hleft]
  have hinjM : Function.Injective
      (rectMatMulVec (rectMatMul Aplus Apert)) := by
    simpa [hMrep] using hinjIdE
  have hinjApert : Function.Injective (rectMatMulVec Apert) := by
    intro x y hxy
    apply hinjM
    simpa [rectMatMulVec_rectMatMul] using
      congrArg (rectMatMulVec Aplus) hxy
  have hRmat : R = rectMatMul (matTranspose Q) Apert := by
    ext i j
    simpa [R, Q, Apert, rectMatMul, matMulRect] using hR i j
  have hQQT : rectMatMul Q (matTranspose Q) = idMatrix n := by
    ext i j
    exact hQ.right_inv i j
  have hfactor : Apert = rectMatMul Q R := by
    calc
      Apert = rectMatMul (idMatrix n) Apert :=
        (rectMatMul_id_left Apert).symm
      _ = rectMatMul (rectMatMul Q (matTranspose Q)) Apert := by
        rw [hQQT]
      _ = rectMatMul Q (rectMatMul (matTranspose Q) Apert) :=
        rectMatMul_assoc Q (matTranspose Q) Apert
      _ = rectMatMul Q R := by rw [<- hRmat]
  have hinjR : Function.Injective (rectMatMulVec R) := by
    intro x y hxy
    apply hinjApert
    have hQxy := congrArg (rectMatMulVec Q) hxy
    have hprod :
        rectMatMulVec (rectMatMul Q R) x =
          rectMatMulVec (rectMatMul Q R) y := by
      simpa [rectMatMulVec_rectMatMul] using hQxy
    simpa [hfactor] using hprod
  obtain ⟨L, hLR⟩ :=
    ch7_exists_rect_left_inverse_of_rectMatMulVec_injective R hinjR
  let LM : Matrix (Fin n) (Fin n) Real := fun i j => L i j
  let RM : Matrix (Fin n) (Fin n) Real := fun i j => R i j
  have hLRmat : LM * RM = 1 := by
    ext i j
    simpa [LM, RM, Matrix.mul_apply, idMatrix] using hLR i j
  have hdet : Matrix.det (R : Matrix (Fin n) (Fin n) Real) ≠ 0 := by
    have hunit : IsUnit RM.det := Matrix.isUnit_det_of_left_inverse hLRmat
    simpa [RM] using (isUnit_iff_ne_zero.mp hunit)
  have hupper : forall i j : Fin n, j.val < i.val -> R i j = 0 := by
    simpa [R, IsUpperTriangular] using fl_householderQR_R_upper fp n A
  exact diag_ne_zero_of_upper_triangular_det_ne_zero n R hupper hdet

/-- Canonical nonsingular-source specialization of the computed-`R`
nonbreakdown theorem. -/
theorem fl_householderQR_R_diag_nonzero_of_source_small
    (fp : FPModel) (n : Nat) (A : Fin n -> Fin n -> Real)
    (hn : 0 < n)
    (hsource : Function.Injective (rectMatMulVec A))
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hsmall :
      Real.sqrt (n : Real) *
          gamma fp (n * householderConstructApplyGammaIndex n) *
          higham19QRSourceKappa2 A < 1) :
    forall i : Fin n, fl_householderQR_R fp n A i i ≠ 0 := by
  have hleft :
      rectMatMul (lsAplusOfGramNonsingInv A) A = idMatrix n :=
    (lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric
      A hsource).1
  apply fl_householderQR_R_diag_nonzero_of_source_left_inverse_small
    fp n A (lsAplusOfGramNonsingInv A) hn hleft hvalid
  simpa [higham19QRSourceKappa2] using hsmall

/-- Theorem 19.5 for the actual QR solve, with computed-`R` nonbreakdown
derived from source nonsingularity and the printed sufficient smallness
condition. -/
theorem higham19_theorem19_5_actual_columnwise_backward_error_of_source_small
    (fp : FPModel) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hn : 0 < n)
    (hsource : Function.Injective (rectMatMulVec A))
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hsmall :
      Real.sqrt (n : Real) *
          gamma fp (n * householderConstructApplyGammaIndex n) *
          higham19QRSourceKappa2 A < 1) :
    Higham19Theorem5ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Theorem5MatrixCoeff fp n)
      (higham19Theorem5RhsCoeff fp n) := by
  apply higham19_theorem19_5_actual_columnwise_backward_error
    fp n A b hn hvalid
  exact fl_householderQR_R_diag_nonzero_of_source_small
    fp n A hn hsource hvalid hsmall

/-- Equation (19.14), nonzero-RHS branch, with computed-`R` nonbreakdown
derived from the source condition. -/
theorem higham19_eq19_14_actual_columnwise_nonzero_rhs_of_source_small
    (fp : FPModel) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hn : 0 < n)
    (hsource : Function.Injective (rectMatMulVec A))
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hfactorSmall :
      Real.sqrt (n : Real) *
          gamma fp (n * householderConstructApplyGammaIndex n) *
          higham19QRSourceKappa2 A < 1)
    (hb : b ≠ 0)
    (hrhsSmall : higham19Theorem5RhsCoeff fp n < 1) :
    Higham19Eq1914ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Eq1914SourceCoeff fp n) := by
  apply higham19_eq19_14_actual_columnwise_nonzero_rhs
    fp n A b hn hvalid
  · exact fl_householderQR_R_diag_nonzero_of_source_small
      fp n A hn hsource hvalid hfactorSmall
  · exact hb
  · exact hrhsSmall

/-- Equation (19.14), zero-RHS branch, with computed-`R` nonbreakdown
derived from the source condition. -/
theorem higham19_eq19_14_actual_columnwise_zero_rhs_of_source_small
    (fp : FPModel) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hn : 0 < n)
    (hsource : Function.Injective (rectMatMulVec A))
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hfactorSmall :
      Real.sqrt (n : Real) *
          gamma fp (n * householderConstructApplyGammaIndex n) *
          higham19QRSourceKappa2 A < 1)
    (hb : b = 0) :
    Higham19Eq1914ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Theorem5MatrixCoeff fp n) := by
  apply higham19_eq19_14_actual_columnwise_zero_rhs
    fp n A b hn hvalid
  · exact fl_householderQR_R_diag_nonzero_of_source_small
      fp n A hn hsource hvalid hfactorSmall
  · exact hb

end

end NumStability
