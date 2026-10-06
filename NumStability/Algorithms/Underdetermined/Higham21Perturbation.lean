-- Algorithms/Underdetermined/Higham21Perturbation.lean
--
-- The arbitrary-absolute-norm first-order and finite-error forms of
-- Higham's Theorem 21.1.

import NumStability.Algorithms.Underdetermined.Higham21RankStability

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.6):
    the source null-space majorant
    `|I - A^+ A| E^T |(A^+)^T x|`, where `x = A^+ b`. -/
noncomputable def higham21Theorem21_1NullspaceMajorant {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  lsAugmentedEq20_7LeftMajorant Aplus A
    (lsComponentwiseTransposeMajorant E z)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.6):
    the source data majorant `|A^+| (f + E|x|)`, where `x = A^+ b`. -/
noncomputable def higham21Theorem21_1DataMajorant {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real) :
    Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  lsAugmentedEq20_8LeftMajorant Aplus
    (lsComponentwiseDataMajorant E f x)

private theorem higham21_rectTransposeMulVec_abs_le_scaled_majorant
    {m n : Nat}
    (DeltaA E : Fin m -> Fin n -> Real) (z : Fin m -> Real) (eps : Real)
    (hDeltaA : forall i j, abs (DeltaA i j) <= eps * E i j) :
    forall j : Fin n,
      abs (rectTransposeMulVec DeltaA z j) <=
        eps * lsComponentwiseTransposeMajorant E z j := by
  intro j
  unfold rectTransposeMulVec lsComponentwiseTransposeMajorant
  calc
    abs (Finset.univ.sum (fun i : Fin m => DeltaA i j * z i)) <=
        Finset.univ.sum (fun i : Fin m => abs (DeltaA i j * z i)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun i : Fin m => abs (DeltaA i j) * abs (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_mul (DeltaA i j) (z i)
    _ <= Finset.univ.sum (fun i : Fin m => (eps * E i j) * abs (z i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hDeltaA i j) (abs_nonneg (z i))
    _ = eps * Finset.univ.sum (fun i : Fin m => E i j * abs (z i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem higham21_domainProjection_residual_abs_le_scaled_majorant
    {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (w W : Fin n -> Real) (eps : Real)
    (hw : forall k, abs (w k) <= eps * W k) :
    forall j : Fin n,
      abs (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) <=
        eps * lsAugmentedEq20_7LeftMajorant Aplus A W j := by
  intro j
  let P := lsAugmentedProjectionBlock Aplus A
  calc
    abs (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) =
        abs (rectMatMulVec P w j) := by
      simpa [P] using
        congrArg abs
          (congrFun (lsAugmentedProjectionBlock_mulVec Aplus A w) j).symm
    _ <= Finset.univ.sum (fun k : Fin n => abs (P j k) * abs (w k)) :=
      abs_rectMatMulVec_le P w j
    _ <= Finset.univ.sum (fun k : Fin n => abs (P j k) * (eps * W k)) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hw k) (abs_nonneg (P j k))
    _ = eps * rectMatMulVec (absMatrixRect P) W j := by
      unfold rectMatMulVec absMatrixRect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = eps * lsAugmentedEq20_7LeftMajorant Aplus A W j := by
      simp only [P, lsAugmentedEq20_7LeftMajorant]

private theorem higham21_scaled_data_majorant
    {m n : Nat}
    (Aplus : Fin n -> Fin m -> Real) (E : Fin m -> Fin n -> Real)
    (f : Fin m -> Real) (x : Fin n -> Real) (eps : Real) (j : Fin n) :
    rectMatMulVec (absMatrixRect Aplus)
        (fun i =>
          eps * f i +
            rectMatMulVec (fun r k => eps * E r k)
              (fun k => abs (x k)) i) j =
      eps *
        lsAugmentedEq20_8LeftMajorant Aplus
          (lsComponentwiseDataMajorant E f x) j := by
  have hinner : forall i : Fin m,
      rectMatMulVec (fun r k => eps * E r k) (fun k => abs (x k)) i =
        eps * rectMatMulVec E (fun k => abs (x k)) i := by
    intro i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hinner]
  unfold lsAugmentedEq20_8LeftMajorant lsComponentwiseDataMajorant absVec
  unfold rectMatMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The null-space majorant in Theorem 21.1 is componentwise nonnegative. -/
theorem higham21Theorem21_1NullspaceMajorant_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hE : forall i j, 0 <= E i j) :
    forall j, 0 <= higham21Theorem21_1NullspaceMajorant A E b j := by
  intro j
  simp only [higham21Theorem21_1NullspaceMajorant,
    lsAugmentedEq20_7LeftMajorant, rectMatMulVec, absMatrixRect,
    lsComponentwiseTransposeMajorant]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hE i k) (abs_nonneg _)

/-- The data majorant in Theorem 21.1 is componentwise nonnegative. -/
theorem higham21Theorem21_1DataMajorant_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i) :
    forall j, 0 <= higham21Theorem21_1DataMajorant A E b f j := by
  intro j
  simp only [higham21Theorem21_1DataMajorant,
    lsAugmentedEq20_8LeftMajorant, lsComponentwiseDataMajorant,
    rectMatMulVec, absMatrixRect, absVec]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (abs_nonneg _)
  apply add_nonneg (hf i)
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hE i k) (abs_nonneg _)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equations (21.6)-(21.7):
    the first-order vector is bounded componentwise by `eps` times the sum of
    the two source majorants. -/
theorem higham21_theorem21_1_firstOrder_componentwise_bound {m n : Nat}
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (eps : Real)
    (hdet : Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hDeltaA : forall i j, abs (DeltaA i j) <= eps * E i j)
    (hDeltab : forall i, abs (Deltab i) <= eps * f i) :
    forall j : Fin n,
      abs (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) j) <=
        eps *
          (higham21Theorem21_1NullspaceMajorant A E b j +
            higham21Theorem21_1DataMajorant A E b f j) := by
  intro j
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let U : Fin n -> Real := lsComponentwiseTransposeMajorant E z
  have hw : forall k, abs (w k) <= eps * U k := by
    intro k
    exact higham21_rectTransposeMulVec_abs_le_scaled_majorant
      DeltaA E z eps hDeltaA k
  have hleft :
      abs (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) <=
        eps * higham21Theorem21_1NullspaceMajorant A E b j := by
    have h :=
      higham21_domainProjection_residual_abs_le_scaled_majorant
        A Aplus w U eps hw j
    simpa [Aplus, x, z, U, higham21Theorem21_1NullspaceMajorant] using h
  have hright :
      rectMatMulVec (absMatrixRect Aplus)
          (fun i =>
            eps * f i +
              rectMatMulVec (fun r k => eps * E r k)
                (fun k => abs (x k)) i) j =
        eps * higham21Theorem21_1DataMajorant A E b f j := by
    simpa [Aplus, x, higham21Theorem21_1DataMajorant] using
      higham21_scaled_data_majorant Aplus E f x eps j
  have hbase :=
    higham21Eq21_7_firstOrder_componentwise_abs_majorant
      A DeltaA (fun i k => eps * E i k)
      b Deltab (fun i => eps * f i) hdet hDeltaA hDeltab j
  calc
    abs (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) j) <=
        abs (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
          rectMatMulVec (absMatrixRect Aplus)
            (fun i =>
              eps * f i +
                rectMatMulVec (fun r k => eps * E r k)
                  (fun k => abs (x k)) i) j := by
      simpa [Aplus, x, z, w, absVec] using hbase
    _ <= eps * higham21Theorem21_1NullspaceMajorant A E b j +
        eps * higham21Theorem21_1DataMajorant A E b f j :=
      add_le_add hleft (le_of_eq hright)
    _ = eps *
        (higham21Theorem21_1NullspaceMajorant A E b j +
          higham21Theorem21_1DataMajorant A E b f j) := by
      ring

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.6), numerator
    form: every absolute vector norm bounds the first-order term by the sum of
    the norms of the two printed majorant vectors. -/
theorem higham21_theorem21_1_firstOrder_numerator_bound {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (eps : Real)
    (hdet : Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (heps : 0 <= eps) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= eps * E i j)
    (hDeltab : forall i, abs (Deltab i) <= eps * f i) :
    nu (realVecToComplex
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A))) <=
      eps *
        (nu (realVecToComplex
            (higham21Theorem21_1NullspaceMajorant A E b)) +
          nu (realVecToComplex
            (higham21Theorem21_1DataMajorant A E b f))) := by
  let left : Fin n -> Real := higham21Theorem21_1NullspaceMajorant A E b
  let right : Fin n -> Real := higham21Theorem21_1DataMajorant A E b f
  let major : Fin n -> Real := fun j => left j + right j
  have hleft : forall j, 0 <= left j := by
    intro j
    exact higham21Theorem21_1NullspaceMajorant_nonneg A E b hE j
  have hright : forall j, 0 <= right j := by
    intro j
    exact higham21Theorem21_1DataMajorant_nonneg A E b f hE hf j
  have hmajor : forall j, 0 <= eps * major j := by
    intro j
    exact mul_nonneg heps (add_nonneg (hleft j) (hright j))
  have hpoint : forall j,
      abs (higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) j) <= eps * major j := by
    intro j
    simpa [left, right, major] using
      higham21_theorem21_1_firstOrder_componentwise_bound
        A DeltaA E b Deltab f eps hdet hDeltaA hDeltab j
  have hmono :
      nu (realVecToComplex
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A))) <=
        nu (realVecToComplex (fun j => eps * major j)) :=
    realVecToComplex_norm_le_of_abs_le hnu habs hmajor hpoint
  have hscale :
      nu (realVecToComplex (fun j => eps * major j)) =
        eps * nu (realVecToComplex major) :=
    realVecToComplex_norm_smul_nonneg hnu eps heps major
  have htri :
      nu (realVecToComplex major) <=
        nu (realVecToComplex left) + nu (realVecToComplex right) := by
    simpa [major] using realVecToComplex_norm_add_le hnu left right
  calc
    nu (realVecToComplex
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A))) <=
        nu (realVecToComplex (fun j => eps * major j)) := hmono
    _ = eps * nu (realVecToComplex major) := hscale
    _ <= eps *
        (nu (realVecToComplex left) + nu (realVecToComplex right)) :=
      mul_le_mul_of_nonneg_left htri heps
    _ = eps *
        (nu (realVecToComplex
            (higham21Theorem21_1NullspaceMajorant A E b)) +
          nu (realVecToComplex
            (higham21Theorem21_1DataMajorant A E b f))) := by
      rfl

private theorem higham21_baseSolution_norm_pos_of_rhs_ne_zero {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hdet : Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0)) :
    0 < nu (realVecToComplex
      (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hAx : rectMatMulVec A x = b := by
    calc
      rectMatMulVec A x = rectMatMulVec (rectMatMul A Aplus) b := by
        simpa [x] using (rectMatMulVec_rectMatMul A Aplus b).symm
      _ = rectMatMulVec (idMatrix m) b := by rw [hRight]
      _ = b := rectMatMulVec_idMatrix b
  have hx : Not (x = 0) := by
    intro hx0
    apply hb
    calc
      b = rectMatMulVec A x := hAx.symm
      _ = 0 := by
        rw [hx0]
        funext i
        unfold rectMatMulVec
        simp
  have hxc : Not (realVecToComplex x = 0) := by
    intro hxc0
    apply hx
    ext j
    have hj := congrArg Complex.re (congrFun hxc0 j)
    simpa [realVecToComplex] using hj
  have hnorm_ne : Not (nu (realVecToComplex x) = 0) := by
    intro hnorm
    exact hxc ((hnu.eq_zero_iff (realVecToComplex x)).mp hnorm)
  simpa [Aplus, x] using
    lt_of_le_of_ne (hnu.nonneg (realVecToComplex x)) (Ne.symm hnorm_ne)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.6), relative
    first-order form for an arbitrary absolute vector norm. -/
theorem higham21_theorem21_1_firstOrder_relative_bound {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (eps : Real)
    (hdet : Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (heps : 0 <= eps) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i)
    (hb : Not (b = 0))
    (hDeltaA : forall i j, abs (DeltaA i j) <= eps * E i j)
    (hDeltab : forall i, abs (Deltab i) <= eps * f i) :
    nu (realVecToComplex
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A))) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) <=
      (eps *
        (nu (realVecToComplex
            (higham21Theorem21_1NullspaceMajorant A E b)) +
          nu (realVecToComplex
            (higham21Theorem21_1DataMajorant A E b f)))) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) := by
  exact div_le_div_of_nonneg_right
    (higham21_theorem21_1_firstOrder_numerator_bound
      nu hnu habs A DeltaA E b Deltab f eps hdet heps hE hf
      hDeltaA hDeltab)
    (le_of_lt
      (higham21_baseSolution_norm_pos_of_rhs_ne_zero
        nu hnu A b hdet hb))

private theorem higham21_realVecToComplex_norm_smul {n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (a : Real) (x : Fin n -> Real) :
    nu (realVecToComplex (fun i => a * x i)) =
      |a| * nu (realVecToComplex x) := by
  have hsmul := hnu.smul (a : Complex) (realVecToComplex x)
  calc
    nu (realVecToComplex (fun i => a * x i)) =
        nu (complexVecSMul (a : Complex) (realVecToComplex x)) := by
      congr 1
      ext i
      simp [realVecToComplex, complexVecSMul]
    _ = norm (a : Complex) * nu (realVecToComplex x) := hsmul
    _ = |a| * nu (realVecToComplex x) := by
      rw [Complex.norm_real, Real.norm_eq_abs]

private theorem
    higham21_realVecToComplex_norm_le_vecNorm2_mul_norm_one {n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu) (x : Fin n -> Real) :
    nu (realVecToComplex x) <=
      vecNorm2 x *
        nu (realVecToComplex (fun _ : Fin n => (1 : Real))) := by
  calc
    nu (realVecToComplex x) <=
        nu (realVecToComplex (fun _ : Fin n => vecNorm2 x)) := by
      exact realVecToComplex_norm_le_of_abs_le hnu habs
        (fun _ => vecNorm2_nonneg x)
        (fun i => abs_coord_le_vecNorm2 x i)
    _ = vecNorm2 x *
        nu (realVecToComplex (fun _ : Fin n => (1 : Real))) := by
      simpa only [mul_one] using
        (realVecToComplex_norm_smul_nonneg hnu
          (vecNorm2 x) (vecNorm2_nonneg x)
          (fun _ : Fin n => (1 : Real)))

/-- The Euclidean fixed-radius remainder estimate in equation (21.7), lifted
    to an arbitrary absolute vector norm by domination with the constant
    vector at `vecNorm2` of the remainder. -/
theorem higham21Eq21_7_exactRemainder_absoluteNorm_le_fixed_radius
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real)
    (rho beta t : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (ht : |t| <= rho) (hG_t_inv : frobNorm G_t_inv <= beta) :
    nu (realVecToComplex
        (higham21Eq21_7ExactRemainder
          A DeltaA b Deltab G_inv G_t_inv t)) <=
      |t| ^ 2 *
        (higham21Eq21_7FixedRadiusCoefficient
            A DeltaA b Deltab G_inv rho beta *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real)))) := by
  let remainder := higham21Eq21_7ExactRemainder
    A DeltaA b Deltab G_inv G_t_inv t
  have hLift :
      nu (realVecToComplex remainder) <=
        vecNorm2 remainder *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real))) :=
    higham21_realVecToComplex_norm_le_vecNorm2_mul_norm_one
      nu hnu habs remainder
  have hVec :
      vecNorm2 remainder <=
        |t| ^ 2 * higham21Eq21_7FixedRadiusCoefficient
          A DeltaA b Deltab G_inv rho beta := by
    simpa [remainder] using
      (higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
        A DeltaA b Deltab G_inv G_t_inv rho beta t
        hrho hbeta ht hG_t_inv)
  calc
    nu (realVecToComplex remainder) <=
        vecNorm2 remainder *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real))) := hLift
    _ <=
        (|t| ^ 2 * higham21Eq21_7FixedRadiusCoefficient
            A DeltaA b Deltab G_inv rho beta) *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real))) :=
      mul_le_mul_of_nonneg_right hVec
        (hnu.nonneg (realVecToComplex (fun _ : Fin n => (1 : Real))))
    _ = |t| ^ 2 *
        (higham21Eq21_7FixedRadiusCoefficient
            A DeltaA b Deltab G_inv rho beta *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real)))) := by
      ring

/-- The imported Euclidean `O(t^2)` remainder estimate in equation (21.7),
    lifted to every absolute vector norm without a finite-dimensional norm
    equivalence assumption. -/
theorem higham21Eq21_7_exactRemainder_absoluteNorm_isBigO
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (G_inv : Fin m -> Fin m -> Real)
    (G_t_inv : Real -> Fin m -> Fin m -> Real)
    (rho beta : Real) (hrho : 0 < rho) (hbeta : 0 <= beta)
    (hG_t_inv : forall t, |t| <= rho -> frobNorm (G_t_inv t) <= beta) :
    (fun t =>
      nu (realVecToComplex
        (higham21Eq21_7ExactRemainder
          A DeltaA b Deltab G_inv (G_t_inv t) t))) =O[nhds 0]
      (fun t : Real => t ^ 2) := by
  let remainder : Real -> Fin n -> Real := fun t =>
    higham21Eq21_7ExactRemainder
      A DeltaA b Deltab G_inv (G_t_inv t) t
  have hLiftO :
      (fun t => nu (realVecToComplex (remainder t))) =O[nhds 0]
        (fun t => vecNorm2 (remainder t)) := by
    apply Asymptotics.IsBigO.of_bound
      (nu (realVecToComplex (fun _ : Fin n => (1 : Real))))
    filter_upwards [] with t
    calc
      norm (nu (realVecToComplex (remainder t))) =
          nu (realVecToComplex (remainder t)) := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (hnu.nonneg (realVecToComplex (remainder t)))]
      _ <= vecNorm2 (remainder t) *
          nu (realVecToComplex (fun _ : Fin n => (1 : Real))) :=
        higham21_realVecToComplex_norm_le_vecNorm2_mul_norm_one
          nu hnu habs (remainder t)
      _ = nu (realVecToComplex (fun _ : Fin n => (1 : Real))) *
          norm (vecNorm2 (remainder t)) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm2_nonneg _)]
        ring
  have hVecO :
      (fun t => vecNorm2 (remainder t)) =O[nhds 0]
        (fun t : Real => t ^ 2) := by
    simpa [remainder] using
      (higham21Eq21_7_exactRemainder_vecNorm2_isBigO
        A DeltaA b Deltab G_inv G_t_inv rho beta
        hrho hbeta hG_t_inv)
  simpa [remainder] using (hLiftO.trans hVecO)

private theorem higham21_theorem21_1_exact_remainder_numerator_bound
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (t : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hdet_t :
      Not
        (Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
            Matrix (Fin m) (Fin m) Real) = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i) :
    nu (realVecToComplex
        (fun j =>
          higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
            higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j)) <=
      |t| *
          (nu (realVecToComplex
              (higham21Theorem21_1NullspaceMajorant A E b)) +
            nu (realVecToComplex
              (higham21Theorem21_1DataMajorant A E b f))) +
        nu (realVecToComplex
          (higham21Eq21_7ExactRemainder A DeltaA b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A DeltaA t)) t)) := by
  let firstOrder := higham21Eq21_7FirstOrder
    A DeltaA b Deltab (undetGramNonsingInv A)
  let remainder := higham21Eq21_7ExactRemainder A DeltaA b Deltab
    (undetGramNonsingInv A)
    (undetGramNonsingInv
      (higham21Eq21_7ScaledMatrix A DeltaA t)) t
  have hDeltaA_one : forall i j,
      abs (DeltaA i j) <= (1 : Real) * E i j := by
    intro i j
    simpa using hDeltaA i j
  have hDeltab_one : forall i,
      abs (Deltab i) <= (1 : Real) * f i := by
    intro i
    simpa using hDeltab i
  have hFirst :
      nu (realVecToComplex firstOrder) <=
        nu (realVecToComplex
            (higham21Theorem21_1NullspaceMajorant A E b)) +
          nu (realVecToComplex
            (higham21Theorem21_1DataMajorant A E b f)) := by
    simpa [firstOrder] using
      (higham21_theorem21_1_firstOrder_numerator_bound
        nu hnu habs A DeltaA E b Deltab f (1 : Real)
        hdet (by norm_num) hE hf hDeltaA_one hDeltab_one)
  have hExpansion :
      (fun j =>
        higham21Eq21_7PerturbedSolution A DeltaA b Deltab
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
          higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j) =
        fun j => t * firstOrder j + remainder j := by
    simpa [firstOrder, remainder] using
      (higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
        A DeltaA b Deltab t hdet hdet_t)
  rw [hExpansion]
  calc
    nu (realVecToComplex (fun j => t * firstOrder j + remainder j)) <=
        nu (realVecToComplex (fun j => t * firstOrder j)) +
          nu (realVecToComplex remainder) :=
      realVecToComplex_norm_add_le hnu
        (fun j => t * firstOrder j) remainder
    _ = |t| * nu (realVecToComplex firstOrder) +
        nu (realVecToComplex remainder) := by
      rw [higham21_realVecToComplex_norm_smul nu hnu t firstOrder]
    _ <= |t| *
          (nu (realVecToComplex
              (higham21Theorem21_1NullspaceMajorant A E b)) +
            nu (realVecToComplex
              (higham21Theorem21_1DataMajorant A E b f))) +
        nu (realVecToComplex remainder) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hFirst (abs_nonneg t)) le_rfl

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1: determinant-facing exact
    finite-error numerator bound.  The first-order coefficient is the two
    source majorant norms and the exact remainder contributes a fixed
    `|t|^2` coefficient. -/
theorem higham21_theorem21_1_finite_error_numerator_bound_of_gram_det_ne_zero
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (rho beta t : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hdet_t :
      Not
        (Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
            Matrix (Fin m) (Fin m) Real) = 0))
    (_hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) (ht : |t| <= rho)
    (hG_t_inv :
      frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA t)) <= beta) :
    nu (realVecToComplex
        (fun j =>
          higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
            higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j)) <=
      |t| *
          (nu (realVecToComplex
              (higham21Theorem21_1NullspaceMajorant A E b)) +
            nu (realVecToComplex
              (higham21Theorem21_1DataMajorant A E b f))) +
        |t| ^ 2 *
          (higham21Eq21_7FixedRadiusCoefficient A DeltaA b Deltab
                (undetGramNonsingInv A) rho beta *
            nu (realVecToComplex (fun _ : Fin n => (1 : Real)))) := by
  have hCore :=
    higham21_theorem21_1_exact_remainder_numerator_bound
      nu hnu habs A DeltaA E b Deltab f t hdet hdet_t
      hE hf hDeltaA hDeltab
  have hRemainder :=
    higham21Eq21_7_exactRemainder_absoluteNorm_le_fixed_radius
      nu hnu habs A DeltaA b Deltab
      (undetGramNonsingInv A)
      (undetGramNonsingInv
        (higham21Eq21_7ScaledMatrix A DeltaA t))
      rho beta t hrho hbeta ht hG_t_inv
  exact hCore.trans (add_le_add_right hRemainder _)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1: determinant-facing exact
    finite-error relative bound for an arbitrary absolute vector norm. -/
theorem higham21_theorem21_1_finite_error_relative_bound_of_gram_det_ne_zero
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (rho beta t : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hdet_t :
      Not
        (Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
            Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) (ht : |t| <= rho)
    (hG_t_inv :
      frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA t)) <= beta) :
    nu (realVecToComplex
        (fun j =>
          higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
            higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j)) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) <=
      (|t| *
            (nu (realVecToComplex
                (higham21Theorem21_1NullspaceMajorant A E b)) +
              nu (realVecToComplex
                (higham21Theorem21_1DataMajorant A E b f))) +
          |t| ^ 2 *
            (higham21Eq21_7FixedRadiusCoefficient A DeltaA b Deltab
                  (undetGramNonsingInv A) rho beta *
              nu (realVecToComplex (fun _ : Fin n => (1 : Real))))) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) := by
  exact div_le_div_of_nonneg_right
    (higham21_theorem21_1_finite_error_numerator_bound_of_gram_det_ne_zero
      nu hnu habs A DeltaA E b Deltab f rho beta t
      hdet hdet_t hb hE hf hDeltaA hDeltab hrho hbeta ht hG_t_inv)
    (le_of_lt
      (higham21_baseSolution_norm_pos_of_rhs_ne_zero
        nu hnu A b hdet hb))

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, source-facing relative
    asymptotic form.  The displayed remainder ratio is explicitly
    `O(t^2)`, and the accompanying inequality is the exact meaning of the
    source's first-order coefficient plus quadratic remainder. -/
theorem higham21_theorem21_1_relative_asymptotic_bound_of_gram_det_ne_zero
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (rho beta : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hdet_t : forall t, |t| <= rho ->
      Not
        (Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
            Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i)
    (hrho : 0 < rho) (hbeta : 0 <= beta)
    (hG_t_inv : forall t, |t| <= rho ->
      frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA t)) <= beta) :
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let remainderRatio : Real -> Real := fun t =>
      nu (realVecToComplex
          (higham21Eq21_7ExactRemainder A DeltaA b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A DeltaA t)) t)) /
        nu (realVecToComplex x)
    And
      (remainderRatio =O[nhds 0] (fun t : Real => t ^ 2))
      (forall t, |t| <= rho ->
        nu (realVecToComplex
            (fun j =>
              higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                    (undetGramNonsingInv
                      (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
                higham21Eq21_7BaseSolution A b
                  (undetGramNonsingInv A) j)) /
            nu (realVecToComplex x) <=
          |t| *
              ((nu (realVecToComplex
                    (higham21Theorem21_1NullspaceMajorant A E b)) +
                  nu (realVecToComplex
                    (higham21Theorem21_1DataMajorant A E b f))) /
                nu (realVecToComplex x)) +
            remainderRatio t) := by
  dsimp only
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  have hxpos : 0 < nu (realVecToComplex x) := by
    simpa [x] using
      (higham21_baseSolution_norm_pos_of_rhs_ne_zero
        nu hnu A b hdet hb)
  constructor
  next =>
    have hRemainderO :
        (fun t =>
          nu (realVecToComplex
            (higham21Eq21_7ExactRemainder A DeltaA b Deltab
              (undetGramNonsingInv A)
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A DeltaA t)) t))) =O[nhds 0]
          (fun t : Real => t ^ 2) :=
      higham21Eq21_7_exactRemainder_absoluteNorm_isBigO
        nu hnu habs A DeltaA b Deltab (undetGramNonsingInv A)
        (fun t =>
          undetGramNonsingInv
            (higham21Eq21_7ScaledMatrix A DeltaA t))
        rho beta hrho hbeta hG_t_inv
    have hNormalized :=
      hRemainderO.const_mul_left (Inv.inv (nu (realVecToComplex x)))
    simpa only [div_eq_mul_inv, mul_comm] using hNormalized
  next =>
    intro t ht
    have hCore :=
      higham21_theorem21_1_exact_remainder_numerator_bound
        nu hnu habs A DeltaA E b Deltab f t hdet (hdet_t t ht)
        hE hf hDeltaA hDeltab
    have hRelative :=
      div_le_div_of_nonneg_right hCore (le_of_lt hxpos)
    calc
      nu (realVecToComplex
          (fun j =>
            higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                  (undetGramNonsingInv
                    (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
              higham21Eq21_7BaseSolution A b
                (undetGramNonsingInv A) j)) /
          nu (realVecToComplex x) <=
        (|t| *
              (nu (realVecToComplex
                  (higham21Theorem21_1NullspaceMajorant A E b)) +
                nu (realVecToComplex
                  (higham21Theorem21_1DataMajorant A E b f))) +
            nu (realVecToComplex
              (higham21Eq21_7ExactRemainder A DeltaA b Deltab
                (undetGramNonsingInv A)
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t))) /
          nu (realVecToComplex x) := hRelative
      _ = |t| *
            ((nu (realVecToComplex
                  (higham21Theorem21_1NullspaceMajorant A E b)) +
                nu (realVecToComplex
                  (higham21Theorem21_1DataMajorant A E b f))) /
              nu (realVecToComplex x)) +
          nu (realVecToComplex
              (higham21Eq21_7ExactRemainder A DeltaA b Deltab
                (undetGramNonsingInv A)
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t)) /
            nu (realVecToComplex x) := by
        ring

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, caller-facing finite relative
    bound.  The printed smallness premise is supplied for the actual
    perturbation `t * DeltaA`; rank stability discharges the perturbed Gram
    determinant needed by the exact expansion. -/
theorem higham21_theorem21_1_finite_error_relative_bound
    {m n : Nat}
    (nu : CVec n -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A DeltaA E : Fin m -> Fin n -> Real)
    (b Deltab f : Fin m -> Real) (rho beta t c : Real)
    (hdet :
      Not (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A)
          (fun i j => t * DeltaA i j)) c)
    (hc : 0 <= c) (hc_lt : c < 1)
    (hb : Not (b = 0))
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i)
    (hDeltaA : forall i j, abs (DeltaA i j) <= E i j)
    (hDeltab : forall i, abs (Deltab i) <= f i)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) (ht : |t| <= rho)
    (hG_t_inv :
      frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA t)) <= beta) :
    nu (realVecToComplex
        (fun j =>
          higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
            higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j)) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) <=
      (|t| *
            (nu (realVecToComplex
                (higham21Theorem21_1NullspaceMajorant A E b)) +
              nu (realVecToComplex
                (higham21Theorem21_1DataMajorant A E b f))) +
          |t| ^ 2 *
            (higham21Eq21_7FixedRadiusCoefficient A DeltaA b Deltab
                  (undetGramNonsingInv A) rho beta *
              nu (realVecToComplex (fun _ : Fin n => (1 : Real))))) /
        nu (realVecToComplex
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b)) := by
  have hdet_t :
      Not
        (Matrix.det
          (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
            Matrix (Fin m) (Fin m) Real) = 0) := by
    simpa only [higham21Eq21_7ScaledMatrix] using
      (higham21_theorem21_1_perturbed_gram_det_ne_zero_of_gram_det_ne_zero
        A (fun i j => t * DeltaA i j) hdet hProduct hc hc_lt)
  exact
    higham21_theorem21_1_finite_error_relative_bound_of_gram_det_ne_zero
      nu hnu habs A DeltaA E b Deltab f rho beta t
      hdet hdet_t hb hE hf hDeltaA hDeltab
      hrho hbeta ht hG_t_inv

end NumStability
