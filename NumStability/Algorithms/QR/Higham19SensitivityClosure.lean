import NumStability.Algorithms.QR.Higham19Sensitivity

namespace NumStability

open scoped BigOperators

namespace H19Sensitivity

/-- Orthonormal rectangular columns preserve the Euclidean vector norm, not
merely bound it. -/
theorem vecNorm2_rectMatMulVec_eq_of_orthonormal {m n : ℕ}
    {Q : Fin m → Fin n → ℝ}
    (hQ : GramSchmidtOrthonormalColumns Q) (x : Fin n → ℝ) :
    vecNorm2 (rectMatMulVec Q x) = vecNorm2 x := by
  unfold vecNorm2
  congr 1
  calc
    vecNorm2Sq (rectMatMulVec Q x) =
        ∑ j : Fin n, ∑ k : Fin n,
          rectangularGram Q j k * (x j * x k) :=
      rectangularGram_quadratic_eq_vecNorm2Sq Q x
    _ = ∑ j : Fin n, ∑ k : Fin n,
          idMatrix n j k * (x j * x k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hQ j k]
    _ = vecNorm2Sq x := idMatrix_quadratic_eq_vecNorm2Sq x

/-- Left multiplication by an orthonormal-column matrix preserves the
Frobenius norm. -/
theorem frobNormRect_rectMatMul_eq_of_orthonormal_left {m n p : ℕ}
    (Q : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    frobNormRect (rectMatMul Q B) = frobNormRect B := by
  unfold frobNormRect
  congr 1
  rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols,
    frobNormSqRect_eq_sum_vecNorm2Sq_cols]
  apply Finset.sum_congr rfl
  intro j _
  have hcol : (fun i : Fin m => rectMatMul Q B i j) =
      rectMatMulVec Q (fun k : Fin n => B k j) := rfl
  rw [hcol]
  rw [← vecNorm2_sq, ← vecNorm2_sq,
    vecNorm2_rectMatMulVec_eq_of_orthonormal hQ]

/-- A nonzero entry forces a positive rectangular Frobenius norm. -/
theorem frobNormRect_pos_of_entry_ne_zero {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hM : M i j ≠ 0) :
    0 < frobNormRect M := by
  unfold frobNormRect
  exact Real.sqrt_pos.2 (frobNormSqRect_pos_of_entry_ne_zero M i j hM)

/-- A nonzero entry forces a positive exact rectangular operator 2-norm. -/
theorem rectOpNorm2_pos_of_entry_ne_zero {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hM : M i j ≠ 0) :
    0 < rectOpNorm2 M := by
  let e : Fin n → ℝ := finiteBasisVec j
  have he : vecNorm2 e = 1 := vecNorm2_finiteBasisVec j
  have hcol : rectMatMulVec M e = fun k => M k j := by
    ext k
    unfold rectMatMulVec e finiteBasisVec
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hcoord := abs_coord_le_vecNorm2 (rectMatMulVec M e) i
  have hbound := rectOpNorm2Le_rectOpNorm2 M e
  rw [hcol] at hcoord
  rw [hcol] at hbound
  rw [he, mul_one] at hbound
  have habs : 0 < |M i j| := abs_pos.mpr hM
  linarith

/-- The diagonal of a product of two upper-triangular finite matrices is the
product of their diagonal entries. -/
theorem rectMatMul_diag_of_upper {n : ℕ}
    (U V : Fin n → Fin n → ℝ)
    (hU : IsUpperTrapezoidal n n U)
    (hV : IsUpperTrapezoidal n n V) (i : Fin n) :
    rectMatMul U V i i = U i i * V i i := by
  unfold rectMatMul
  rw [Finset.sum_eq_single i]
  · intro k _ hki
    by_cases hlt : k.val < i.val
    · rw [hU i k hlt, zero_mul]
    · have hgt : i.val < k.val := by
        have hne : k.val ≠ i.val := by
          intro h
          exact hki (Fin.ext h)
        omega
      rw [hV k i hgt, mul_zero]
  · simp

/-- Exact squared-Frobenius expansion around the identity. -/
theorem frobNormSqRect_sub_id_eq {n : ℕ}
    (S : Fin n → Fin n → ℝ) :
    frobNormSqRect (fun i j => S i j - idMatrix n i j) =
      frobNormSqRect S + (n : ℝ) - 2 * ∑ i : Fin n, S i i := by
  unfold frobNormSqRect idMatrix
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n,
        2 * S i j * (if i = j then 1 else 0)) =
        2 * ∑ i : Fin n, S i i := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          2 * S i j * (if i = j then 1 else 0)) =
          ∑ i : Fin n, 2 * S i i := by simp
      _ = 2 * ∑ i : Fin n, S i i := by rw [Finset.mul_sum]
  have hid :
      (∑ _i : Fin n, ∑ j : Fin n,
        (if _i = j then (1 : ℝ) else 0) ^ 2) = (n : ℝ) := by
    simp
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        (S i j - if i = j then 1 else 0) ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n,
          (S i j ^ 2 - 2 * S i j * (if i = j then 1 else 0) +
            (if i = j then 1 else 0) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i : Fin n, ∑ j : Fin n, S i j ^ 2) -
          (∑ i : Fin n, ∑ j : Fin n,
            2 * S i j * (if i = j then 1 else 0)) +
          (∑ i : Fin n, ∑ j : Fin n,
            (if i = j then (1 : ℝ) else 0) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i : Fin n, ∑ j : Fin n, S i j ^ 2) +
          (n : ℝ) - 2 * ∑ i : Fin n, S i i := by
      rw [hcross, hid]
      ring

/-- Source-uniform positive-diagonal branch selection.

Put `D = ΔA R⁻¹` and `T = ΔR R⁻¹`.  If
`||D||_F < 1/(20(n+1))`, the nonnegative-diagonal normalization of both QR
factors rules out the large root of the quadratic Gram equation, and

`||T||_F ≤ 6 ||D||_F`.

The constants depend only on the column dimension (in fact the Lipschitz
coefficient is universal); no continuity, compactness, or target-bearing
small-root certificate is assumed. -/
theorem economyQR_scaledRVariation_frob_le_six_of_small {m n : ℕ}
    {A Q dA dQ : Fin m → Fin n → ℝ}
    {R dR Rinv : Fin n → Fin n → ℝ}
    (hbase : EconomyQR A Q R)
    (hpert : EconomyQR (add A dA) (add Q dQ) (add R dR))
    (hInv : IsInverse n R Rinv)
    (hsmall : frobNormRect (rectMatMul dA Rinv) <
      1 / (20 * ((n : ℝ) + 1))) :
    frobNormRect (scaledRVariation dR Rinv) ≤
      6 * frobNormRect (rectMatMul dA Rinv) := by
  let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
  let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
  let S : Fin n → Fin n → ℝ := add (idMatrix n) T
  let Qp : Fin m → Fin n → ℝ := add Q dQ
  let d : ℝ := frobNormRect D
  let t : ℝ := frobNormRect T
  have hd_nonneg : 0 ≤ d := frobNormRect_nonneg D
  have ht_nonneg : 0 ≤ t := frobNormRect_nonneg T
  have hden : 0 < 20 * ((n : ℝ) + 1) := by positivity
  have hd_small : d < 1 / (20 * ((n : ℝ) + 1)) := by
    simpa [d, D] using hsmall
  have hd_one : d < 1 := by
    have hden20 : 20 ≤ 20 * ((n : ℝ) + 1) := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    have hone : 1 / (20 * ((n : ℝ) + 1)) ≤ 1 := by
      have hfrac : 1 / (20 * ((n : ℝ) + 1)) ≤ (1 / 20 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20) hden20
      exact hfrac.trans (by norm_num)
    exact hd_small.trans_le hone
  have ha_pos : 0 < 1 - d := sub_pos.mpr hd_one
  have hDcert : rectOpNorm2Le D d :=
    rectOpNorm2Le_of_frobNormRect_le D (by simp [d])
  have hfac : add Q D = rectMatMul Qp S := by
    simpa [D, T, S, Qp] using
      (economyQR_normalized_perturbation_factorization
        hbase hpert hInv.2)
  have hQnorm : ∀ x : Fin n → ℝ,
      vecNorm2 (rectMatMulVec Q x) = vecNorm2 x :=
    vecNorm2_rectMatMulVec_eq_of_orthonormal hbase.orthonormal
  have hQpnorm : ∀ x : Fin n → ℝ,
      vecNorm2 (rectMatMulVec Qp x) = vecNorm2 x :=
    vecNorm2_rectMatMulVec_eq_of_orthonormal hpert.orthonormal
  have haction : ∀ x : Fin n → ℝ,
      rectMatMulVec (add Q D) x =
        rectMatMulVec Qp (rectMatMulVec S x) := by
    intro x
    rw [hfac, rectMatMulVec_rectMatMul]
  have hQDlower : ∀ x : Fin n → ℝ,
      (1 - d) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec (add Q D) x) := by
    intro x
    have hsplit := rectMatMulVec_mat_add Q D x
    have htri := vecNorm2_add_le
      (rectMatMulVec (add Q D) x)
      (fun i => -rectMatMulVec D x i)
    have hsum :
        (fun i => rectMatMulVec (add Q D) x i +
          -rectMatMulVec D x i) = rectMatMulVec Q x := by
      ext i
      have hi : rectMatMulVec (add Q D) x i =
          rectMatMulVec Q x i + rectMatMulVec D x i := by
        simpa [add] using congrFun hsplit i
      rw [hi]
      ring
    rw [hsum, hQnorm x] at htri
    have hD := hDcert x
    have hneg : vecNorm2 (fun i => -rectMatMulVec D x i) =
        vecNorm2 (rectMatMulVec D x) := vecNorm2_neg _
    rw [hneg] at htri
    nlinarith
  have hSlower : ∀ x : Fin n → ℝ,
      (1 - d) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec S x) := by
    intro x
    have h := hQDlower x
    rw [haction x, hQpnorm (rectMatMulVec S x)] at h
    exact h
  have hSupper : IsUpperTrapezoidal n n S := by
    have hTupper := economyQR_scaledRVariation_upper hbase hpert hInv
    intro i j hji
    have hij : i ≠ j := by omega
    simp [S, T, add, idMatrix, hTupper i j hji, hij]
  have hQDinj : Function.Injective (rectMatMulVec (add Q D)) := by
    apply rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
      (M := Q) (Delta := D) (mu := 1) (eta := d)
    · intro x
      rw [hQnorm x]
      simp
    · exact hDcert
    · exact hd_one
  have hSinj : Function.Injective (rectMatMulVec S) := by
    intro x y hxy
    apply hQDinj
    calc
      rectMatMulVec (add Q D) x =
          rectMatMulVec Qp (rectMatMulVec S x) := haction x
      _ = rectMatMulVec Qp (rectMatMulVec S y) := by rw [hxy]
      _ = rectMatMulVec (add Q D) y := (haction y).symm
  have hdetS : Matrix.det (S : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    let SM : Matrix (Fin n) (Fin n) ℝ := Matrix.of S
    have hmatrixInj : Function.Injective
        SM.mulVec := by
      simpa [SM, Matrix.mulVec, dotProduct, rectMatMulVec] using hSinj
    have hunit : IsUnit SM :=
      Matrix.mulVec_injective_iff_isUnit.mp hmatrixInj
    have hdetunit : IsUnit (Matrix.det SM) :=
      (Matrix.isUnit_iff_isUnit_det SM).mp hunit
    simpa [SM] using (isUnit_iff_ne_zero.mp hdetunit)
  let Sinv : Fin n → Fin n → ℝ := nonsingInv n S
  have hSinv : IsInverse n S Sinv :=
    isInverse_nonsingInv_of_det_ne_zero n S hdetS
  have hSinvUpper : IsUpperTrapezoidal n n Sinv :=
    upper_inverse_of_isInverse hSupper hSinv
  have hRinvUpper : IsUpperTrapezoidal n n Rinv :=
    upper_inverse_of_isInverse hbase.upper hInv
  have hRdiagProd : ∀ i : Fin n, Rinv i i * R i i = 1 := by
    intro i
    have hi := hInv.1 i i
    change rectMatMul Rinv R i i = idMatrix n i i at hi
    rw [rectMatMul_diag_of_upper Rinv R hRinvUpper hbase.upper i] at hi
    simpa [idMatrix] using hi
  have hRdiagPos : ∀ i : Fin n, 0 < R i i := by
    intro i
    have hne : R i i ≠ 0 := by
      intro hz
      have hp := hRdiagProd i
      rw [hz, mul_zero] at hp
      norm_num at hp
    exact lt_of_le_of_ne (hbase.diagonal_nonnegative i) (Ne.symm hne)
  have hRinvDiagPos : ∀ i : Fin n, 0 < Rinv i i := by
    intro i
    have hp := hRdiagProd i
    have hr := hRdiagPos i
    nlinarith
  have hSproduct : S = rectMatMul (add R dR) Rinv := by
    have hRRinv : rectMatMul R Rinv = idMatrix n := by
      ext i j
      exact hInv.2 i j
    calc
      S = add (idMatrix n) (rectMatMul dR Rinv) := by
          rfl
      _ = add (rectMatMul R Rinv) (rectMatMul dR Rinv) := by
          rw [hRRinv]
      _ = rectMatMul (add R dR) Rinv := by
          symm
          exact rectMatMul_add_left R dR Rinv
  have hSdiagNonneg : ∀ i : Fin n, 0 ≤ S i i := by
    intro i
    rw [hSproduct,
      rectMatMul_diag_of_upper (add R dR) Rinv hpert.upper hRinvUpper i]
    exact mul_nonneg (hpert.diagonal_nonnegative i)
      (le_of_lt (hRinvDiagPos i))
  have hSdiagPos : ∀ i : Fin n, 0 < S i i := by
    have hne := diag_ne_zero_of_upper_triangular_det_ne_zero
      n S hSupper hdetS
    intro i
    exact lt_of_le_of_ne (hSdiagNonneg i) (Ne.symm (hne i))
  have hSinvAction : ∀ y : Fin n → ℝ,
      rectMatMulVec S (rectMatMulVec Sinv y) = y := by
    intro y
    rw [← rectMatMulVec_rectMatMul]
    have hright : rectMatMul S Sinv = idMatrix n := by
      ext i j
      exact hSinv.2 i j
    rw [hright, rectMatMulVec_idMatrix]
  have hSinvCert : rectOpNorm2Le Sinv (1 / (1 - d)) := by
    intro y
    have hlower := hSlower (rectMatMulVec Sinv y)
    rw [hSinvAction y] at hlower
    have hdiv : vecNorm2 (rectMatMulVec Sinv y) ≤
        vecNorm2 y / (1 - d) :=
      (le_div_iff₀ ha_pos).2 (by
        simpa [mul_comm] using hlower)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hSinvDiag : ∀ i : Fin n, Sinv i i = 1 / S i i := by
    intro i
    have hi := hSinv.1 i i
    change rectMatMul Sinv S i i = idMatrix n i i at hi
    rw [rectMatMul_diag_of_upper Sinv S hSinvUpper hSupper i] at hi
    have hne := ne_of_gt (hSdiagPos i)
    apply (eq_div_iff hne).2
    simpa [idMatrix] using hi
  have hSdiagLower : ∀ i : Fin n, 1 - d ≤ S i i := by
    intro i
    let e : Fin n → ℝ := finiteBasisVec i
    have he : vecNorm2 e = 1 := vecNorm2_finiteBasisVec i
    have hcol : rectMatMulVec Sinv e = fun k => Sinv k i := by
      ext k
      unfold rectMatMulVec e finiteBasisVec
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hcoord := abs_coord_le_vecNorm2 (rectMatMulVec Sinv e) i
    have hbound := hSinvCert e
    rw [hcol] at hcoord
    rw [hcol] at hbound
    rw [he, mul_one] at hbound
    have hinvle : 1 / S i i ≤ 1 / (1 - d) := by
      rw [← hSinvDiag i]
      have hpos : 0 < Sinv i i := by
        rw [hSinvDiag i]
        exact one_div_pos.mpr (hSdiagPos i)
      rw [abs_of_pos hpos] at hcoord
      exact hcoord.trans hbound
    exact le_of_one_div_le_one_div (hSdiagPos i) hinvle
  have hSupperCert : rectOpNorm2Le S (1 + d) := by
    intro x
    have hsplit := rectMatMulVec_mat_add Q D x
    have htri := vecNorm2_add_le (rectMatMulVec Q x) (rectMatMulVec D x)
    have hnormQD : vecNorm2 (rectMatMulVec (add Q D) x) ≤
        vecNorm2 (rectMatMulVec Q x) + vecNorm2 (rectMatMulVec D x) := by
      unfold add
      rw [hsplit]
      exact htri
    rw [haction x, hQpnorm (rectMatMulVec S x), hQnorm x] at hnormQD
    have hD := hDcert x
    nlinarith
  have hSfrobSq : frobNormSqRect S ≤ (n : ℝ) * (1 + d) ^ 2 :=
    frobNormSqRect_le_card_mul_sq_of_rectOpNorm2Le
      S (by nlinarith) hSupperCert
  have hdiagSum : (n : ℝ) * (1 - d) ≤ ∑ i : Fin n, S i i := by
    calc
      (n : ℝ) * (1 - d) = ∑ _i : Fin n, (1 - d) := by
        simp [mul_sub]
      _ ≤ ∑ i : Fin n, S i i :=
        Finset.sum_le_sum (fun i _ => hSdiagLower i)
  have hTsub : T = fun i j => S i j - idMatrix n i j := by
    funext i j
    simp [S, add]
  have ht_sq : t ^ 2 = frobNormSqRect T := by
    simpa [t] using frobNormRect_sq T
  have htSqBound : t ^ 2 ≤ (n : ℝ) * (4 * d + d ^ 2) := by
    rw [ht_sq, hTsub, frobNormSqRect_sub_id_eq]
    calc
      frobNormSqRect S + (n : ℝ) - 2 * ∑ i : Fin n, S i i ≤
          ((n : ℝ) * (1 + d) ^ 2) + (n : ℝ) -
            2 * ((n : ℝ) * (1 - d)) := by nlinarith
      _ = (n : ℝ) * (4 * d + d ^ 2) := by ring
  have hd_sq_le : d ^ 2 ≤ d := by nlinarith
  have hscaled : 20 * (n : ℝ) * d < 1 := by
    have hmul : d * (20 * ((n : ℝ) + 1)) < 1 :=
      (lt_div_iff₀ hden).mp (by simpa using hd_small)
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have htSqQuarter : t ^ 2 < (1 / 4 : ℝ) := by
    have haux : (n : ℝ) * (4 * d + d ^ 2) < (1 / 4 : ℝ) := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    exact htSqBound.trans_lt haux
  have ht_half : t < (1 / 2 : ℝ) := by nlinarith
  have hmajorant : t ≤
      (2 * d + d ^ 2 + t ^ 2) / Real.sqrt 2 := by
    simpa [d, t, D, T] using
      (economyQR_scaledRVariation_frob_quadratic_majorant
        hbase hpert hInv)
  have hnum_nonneg : 0 ≤ 2 * d + d ^ 2 + t ^ 2 := by positivity
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmajorant' : t ≤ 2 * d + d ^ 2 + t ^ 2 :=
    hmajorant.trans (div_le_self hnum_nonneg hsqrt)
  have ht_sq_half : t ^ 2 ≤ t / 2 := by nlinarith
  have hfinal : t ≤ 6 * d := by nlinarith
  simpa [t, d, T, D] using hfinal

/-- Stewart's source-strength local QR sensitivity theorem, equations
(19.35a/b), with a coefficient chosen before the row dimension and all matrix
data.  The universal coefficient `7` is stronger than the printed
dimension-only `c_n`; the neighborhood may depend on the base factorization,
as "sufficiently small" permits. -/
theorem stewartLocalSensitivitySource_proved (n : ℕ) :
    StewartLocalSensitivitySource n := by
  unfold StewartLocalSensitivitySource
  refine ⟨7, by norm_num, ?_⟩
  intro m hnm A Q R Rinv hbase hInv
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro dA dQ dR _hsmall _hpert
    have hdQ : dQ = 0 := Subsingleton.elim _ _
    have hdR : dR = 0 := Subsingleton.elim _ _
    rw [hdQ, hdR]
    simp [frobNormRect, frobNormSqRect]
  · let rho : ℝ := rectOpNorm2 Rinv
    let B : ℝ := 20 * ((n : ℝ) + 1)
    let delta : ℝ := 1 / (B * (rho + 1))
    have hrho : 0 ≤ rho := rectOpNorm2_nonneg Rinv
    have hB : 0 < B := by positivity
    have hrho1 : 0 < rho + 1 := by linarith
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    refine ⟨delta, hdelta, ?_⟩
    intro dA dQ dR hdA hpert
    let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
    let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
    let da : ℝ := frobNormRect dA
    let dn : ℝ := frobNormRect D
    let tn : ℝ := frobNormRect T
    have hda : 0 ≤ da := frobNormRect_nonneg dA
    have hforcing : dn ≤ da * rho := by
      simpa [dn, da, rho, D] using
        (stewart_forcing_frobNormRect_le dA Rinv)
    have hdaDelta : da < delta := by simpa [da] using hdA
    have hprod : da * (B * (rho + 1)) < 1 := by
      apply (lt_div_iff₀ (mul_pos hB hrho1)).mp
      simpa [delta] using hdaDelta
    have hdaRho1 : da * (rho + 1) < 1 / B := by
      apply (lt_div_iff₀ hB).2
      nlinarith
    have hdarho : da * rho ≤ da * (rho + 1) := by nlinarith
    have hDsmall : dn < 1 / (20 * ((n : ℝ) + 1)) := by
      have : dn < 1 / B := hforcing.trans_lt (hdarho.trans_lt hdaRho1)
      simpa [B] using this
    have hT : tn ≤ 6 * dn := by
      simpa [tn, dn, T, D] using
        (economyQR_scaledRVariation_frob_le_six_of_small
          hbase hpert hInv (by simpa [D] using hDsmall))
    have hQ : frobNormRect dQ ≤ 7 * dn := by
      have hrecover := economyQR_factorVariation_frob_le_forcing_add_scaledR
        hbase hpert hInv.2
      dsimp only at hrecover
      calc
        frobNormRect dQ ≤ dn + tn := by simpa [dn, tn, D, T] using hrecover
        _ ≤ dn + 6 * dn := by linarith
        _ = 7 * dn := by ring
    have hRinvUpper : IsUpperTrapezoidal n n Rinv :=
      upper_inverse_of_isInverse hbase.upper hInv
    have hdiagProd : ∀ i : Fin n, Rinv i i * R i i = 1 := by
      intro i
      have hi := hInv.1 i i
      change rectMatMul Rinv R i i = idMatrix n i i at hi
      rw [rectMatMul_diag_of_upper Rinv R hRinvUpper hbase.upper i] at hi
      simpa [idMatrix] using hi
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hRentry : R i0 i0 ≠ 0 := by
      intro hz
      have hp := hdiagProd i0
      rw [hz, mul_zero] at hp
      norm_num at hp
    have hRpos : 0 < frobNormRect R :=
      frobNormRect_pos_of_entry_ne_zero R i0 i0 hRentry
    have hAnorm : frobNormRect A = frobNormRect R := by
      rw [hbase.factorization]
      exact frobNormRect_rectMatMul_eq_of_orthonormal_left
        Q R hbase.orthonormal
    have hApos : 0 < frobNormRect A := by rw [hAnorm]; exact hRpos
    have hRrecover :=
      deltaR_frobNormRect_le_scaledRVariation_mul_frobNormRect
        (R := R) (dR := dR) (Rinv := Rinv) hInv
    have hRratio : frobNormRect dR / frobNormRect R ≤ 6 * dn := by
      apply (div_le_iff₀ hRpos).2
      calc
        frobNormRect dR ≤ tn * frobNormRect R := by
          simpa [tn, T] using hRrecover
        _ ≤ (6 * dn) * frobNormRect R :=
          mul_le_mul_of_nonneg_right hT (frobNormRect_nonneg R)
    have hcommon : 7 * dn ≤ 7 * (da * rho) :=
      mul_le_mul_of_nonneg_left hforcing (by norm_num)
    have hcondition :
        7 * (frobNormRect A * rectOpNorm2 Rinv) *
            (frobNormRect dA / frobNormRect A) =
          7 * (da * rho) := by
      have hAne : frobNormRect A ≠ 0 := ne_of_gt hApos
      dsimp [da, rho]
      field_simp
    rw [hcondition]
    constructor
    · exact hRratio.trans (by nlinarith [hcommon])
    · exact hQ.trans hcommon

/-- A closed proof of the literal Zha source statement (19.36).  The
dimension-only first-order coefficient may be taken to be `7n`; the proof is
actually stronger than the printed `O(epsilon^2)` statement, since the local
remainder coefficient is zero. -/
theorem zhaColumnwiseSensitivity_proved {m n : ℕ}
    (hnm : n ≤ m) : ZhaColumnwiseSensitivity m n := by
  refine ⟨hnm, ?_⟩
  by_cases hn : n = 0
  · subst n
    refine ⟨0, by norm_num, ?_⟩
    intro A Q R Rinv G _hbase _hInv _hGnonneg _hGnorm
    refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
    intro epsilon dA dQ dR _hepsilon _hepsilonSmall _hweighted _hpert
    have hdQ : dQ = 0 := Subsingleton.elim _ _
    have hdR : dR = 0 := Subsingleton.elim _ _
    have hR : R = 0 := Subsingleton.elim _ _
    rw [hdQ, hdR, hR]
    have hzeroOp : ∀ {p : ℕ} (M : Fin p → Fin 0 → ℝ),
        rectOpNorm2 M = 0 := by
      intro p M
      apply le_antisymm
      · exact rectOpNorm2_le_of_rectOpNorm2Le M (by norm_num) (by
          intro x
          simp [rectMatMulVec, vecNorm2, vecNorm2Sq])
      · exact rectOpNorm2_nonneg M
    rw [hzeroOp, hzeroOp, hzeroOp]
    constructor
    · simp
    · simp
  · let N : ℝ := n
    let c : ℝ := 7 * N
    have hN : 0 < N := by
      dsimp [N]
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    refine ⟨c, hc, ?_⟩
    intro A Q R Rinv G hbase hInv hGnonneg hGnorm
    let z : ℝ := rectOpNorm2 (zhaConditionMatrix R Rinv)
    let B : ℝ := 20 * (N + 1)
    let delta : ℝ := 1 / (B * (N * z + 1))
    have hz : 0 ≤ z := rectOpNorm2_nonneg _
    have hB : 0 < B := by
      dsimp [B]
      positivity
    have hNz1 : 0 < N * z + 1 := by positivity
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    refine ⟨0, delta, by norm_num, hdelta, ?_⟩
    intro epsilon dA dQ dR hepsilon hepsilonSmall hweighted hpert
    let D : Fin m → Fin n → ℝ := rectMatMul dA Rinv
    let T : Fin n → Fin n → ℝ := scaledRVariation dR Rinv
    let dn : ℝ := frobNormRect D
    let tn : ℝ := frobNormRect T
    have hforcingSource := zha_forcing_frobNormRect_le_of_source
      hnm (R := R) (Rinv := Rinv) hbase hepsilon hGnonneg hGnorm hweighted
    have hsqrt : Real.sqrt N * Real.sqrt N = N := by
      exact Real.mul_self_sqrt (by positivity)
    have hforcing : dn ≤ N * epsilon * z := by
      calc
        dn ≤ Real.sqrt N * (epsilon * (Real.sqrt N * z)) := by
          simpa [dn, D, N, z] using hforcingSource
        _ = N * epsilon * z := by
          calc
            Real.sqrt N * (epsilon * (Real.sqrt N * z)) =
                (Real.sqrt N * Real.sqrt N) * epsilon * z := by ring
            _ = N * epsilon * z := by rw [hsqrt]
    have hepsilonProd : epsilon * (B * (N * z + 1)) < 1 := by
      apply (lt_div_iff₀ (mul_pos hB hNz1)).mp
      simpa [delta] using hepsilonSmall
    have hepsilonNz1 : epsilon * (N * z + 1) < 1 / B := by
      apply (lt_div_iff₀ hB).2
      nlinarith
    have hNz : N * epsilon * z ≤ epsilon * (N * z + 1) := by
      nlinarith
    have hDsmall : dn < 1 / (20 * ((n : ℝ) + 1)) := by
      have : dn < 1 / B := hforcing.trans_lt (hNz.trans_lt hepsilonNz1)
      simpa [B, N] using this
    have hT : tn ≤ 6 * dn := by
      simpa [tn, dn, T, D] using
        (economyQR_scaledRVariation_frob_le_six_of_small
          hbase hpert hInv (by simpa [D] using hDsmall))
    have hQfrob : frobNormRect dQ ≤ 7 * dn := by
      have hrecover := economyQR_factorVariation_frob_le_forcing_add_scaledR
        hbase hpert hInv.2
      dsimp only at hrecover
      calc
        frobNormRect dQ ≤ dn + tn := by
          simpa [dn, tn, D, T] using hrecover
        _ ≤ dn + 6 * dn := by linarith
        _ = 7 * dn := by ring
    have hQop : rectOpNorm2 dQ ≤ frobNormRect dQ :=
      rectOpNorm2_le_of_rectOpNorm2Le dQ (frobNormRect_nonneg dQ)
        (rectOpNorm2Le_of_frobNormRect_le dQ le_rfl)
    have hRinvUpper : IsUpperTrapezoidal n n Rinv :=
      upper_inverse_of_isInverse hbase.upper hInv
    have hdiagProd : ∀ i : Fin n, Rinv i i * R i i = 1 := by
      intro i
      have hi := hInv.1 i i
      change rectMatMul Rinv R i i = idMatrix n i i at hi
      rw [rectMatMul_diag_of_upper Rinv R hRinvUpper hbase.upper i] at hi
      simpa [idMatrix] using hi
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hRentry : R i0 i0 ≠ 0 := by
      intro hzR
      have hp := hdiagProd i0
      rw [hzR, mul_zero] at hp
      norm_num at hp
    have hRpos : 0 < rectOpNorm2 R :=
      rectOpNorm2_pos_of_entry_ne_zero R i0 i0 hRentry
    have hRrecover :=
      deltaR_rectOpNorm2_le_scaledRVariation_mul_rectOpNorm2
        (R := R) (dR := dR) (Rinv := Rinv) hInv
    have hTop : rectOpNorm2 T ≤ tn := by
      exact rectOpNorm2_le_of_rectOpNorm2Le T (frobNormRect_nonneg T)
        (rectOpNorm2Le_of_frobNormRect_le T le_rfl)
    have hRratio : rectOpNorm2 dR / rectOpNorm2 R ≤ 6 * dn := by
      apply (div_le_iff₀ hRpos).2
      calc
        rectOpNorm2 dR ≤ rectOpNorm2 T * rectOpNorm2 R := by
          simpa [T] using hRrecover
        _ ≤ tn * rectOpNorm2 R :=
          mul_le_mul_of_nonneg_right hTop (rectOpNorm2_nonneg R)
        _ ≤ (6 * dn) * rectOpNorm2 R :=
          mul_le_mul_of_nonneg_right hT (rectOpNorm2_nonneg R)
    have hcommon : 7 * dn ≤ 7 * (N * epsilon * z) :=
      mul_le_mul_of_nonneg_left hforcing (by norm_num)
    have hcommonR : 6 * dn ≤ 7 * (N * epsilon * z) := by
      have hdn : 0 ≤ dn := frobNormRect_nonneg D
      have htarget : 0 ≤ N * epsilon * z := by positivity
      nlinarith [hforcing]
    have htarget :
        c * epsilon * rectOpNorm2 (zhaConditionMatrix R Rinv) +
            0 * epsilon ^ 2 =
          7 * (N * epsilon * z) := by
      dsimp [c, z]
      ring
    rw [htarget]
    constructor
    · exact hRratio.trans hcommonR
    · exact hQop.trans (hQfrob.trans hcommon)

end H19Sensitivity

end NumStability
