-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The scalar square endpoint of equation (21.11).

import NumStability.Algorithms.Underdetermined.Higham21Equation21_11

namespace NumStability

set_option maxHeartbeats 1200000

/-- In the scalar square case the nullspace component of the first-order
    perturbation vanishes.  The remaining component therefore has the printed
    `n * eta * cond2(A)` bound with `n = 1`. -/
theorem higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_scalar
    (A DeltaA : Fin 1 -> Fin 1 -> Real) (b : Fin 1 -> Real)
    {eta : Real}
    (hdet : Matrix.det (rectGram A : Matrix (Fin 1) (Fin 1) Real) ≠ 0)
    (heta : 0 <= eta)
    (hrow : forall i : Fin 1,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i) :
    vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) <=
      (1 : Real) * eta *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let Aplus : Fin 1 -> Fin 1 -> Real := undetAplusOfGramNonsingInv A
  let x : Fin 1 -> Real := rectMatMulVec Aplus b
  let z : Fin 1 -> Real := rectTransposeMulVec Aplus x
  let w : Fin 1 -> Real := rectTransposeMulVec DeltaA z
  let p : Fin 1 -> Real := fun j =>
    w j - rectMatMulVec Aplus (rectMatMulVec A w) j
  let v : Fin 1 -> Real := rectMatMulVec Aplus (rectMatMulVec DeltaA x)
  let q : Fin 1 -> Real :=
    rectMatMulVec Aplus
      (fun i => (0 : Real) - rectMatMulVec DeltaA x i)
  let B : Fin 1 -> Fin 1 -> Real := rectMatMul Aplus DeltaA
  let cond : Real := higham21Cond2With A Aplus
  let rho : Real := eta * Real.sqrt (1 : Real) * cond
  have hRight : rectMatMul A Aplus = idMatrix 1 := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hLeft : rectMatMul Aplus A = idMatrix 1 := by
    funext i j
    fin_cases i
    fin_cases j
    have h00 := congrFun (congrFun hRight (0 : Fin 1)) (0 : Fin 1)
    simpa [rectMatMul, idMatrix, mul_comm] using h00
  have hcond : 0 <= cond := by
    simpa [cond] using higham21Cond2With_nonneg A Aplus
  have hrho : 0 <= rho := by
    exact mul_nonneg (mul_nonneg heta (Real.sqrt_nonneg _)) hcond
  have hB : rectOpNorm2Le B rho := by
    simpa [B, rho, cond] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA Aplus eta heta hrow
  have hv : vecNorm2 v <= rho * vecNorm2 x := by
    simpa [v, B, rectMatMulVec_rectMatMul] using hB x
  have hqEq : q = fun j => -v j := by
    ext j
    unfold q v rectMatMulVec
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hq : vecNorm2 q <= rho * vecNorm2 x := by
    rw [hqEq, vecNorm2_neg]
    exact hv
  have hAw : rectMatMulVec Aplus (rectMatMulVec A w) = w := by
    rw [<- rectMatMulVec_rectMatMul, hLeft]
    ext i
    fin_cases i
    simp [rectMatMulVec, idMatrix]
  have hp : p = 0 := by
    ext j
    simp [p, hAw]
  have hfirst : higham21Eq21_11FirstOrder A DeltaA b = q := by
    ext j
    change w j - rectMatMulVec Aplus (rectMatMulVec A w) j -
        rectMatMulVec Aplus (rectMatMulVec DeltaA x) j = q j
    have hpj := congrFun hp j
    rw [hqEq]
    simp [p] at hpj
    dsimp [v]
    linarith
  rw [hfirst]
  have hsqrt : Real.sqrt (1 : Real) = 1 := by norm_num
  simpa [rho, cond, x, Aplus, hsqrt] using hq

/-- Dimension-polymorphic wrapper for the scalar first-order estimate.  The
    hypotheses `0 < m`, `m <= n`, and `n <= 1` force `m = n = 1`. -/
theorem higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_of_card_le_one
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    {eta : Real} (hm : 0 < m) (hmn : m <= n) (hn : n <= 1)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (heta : 0 <= eta)
    (hrow : forall i : Fin m,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i) :
    vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) <=
      (n : Real) * eta *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  have hm1 : m = 1 := by omega
  have hn1 : n = 1 := by omega
  subst m
  subst n
  simpa using
    higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_scalar
      A DeltaA b hdet heta hrow

/-- Higham, 2nd ed., Chapter 21, equation (21.11), for the scalar square
    system `m = n = 1`.  The output is the actual rounded Householder Q-method
    output.  The printed `O(u^2)` term is replaced by the same explicit finite
    `eta^2 * C` remainder used by the higher-dimensional theorem. -/
theorem higham21_eq21_11_computed_qhat_relative_forward_error_quadratic_scalar
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hscalar : m + k <= 1)
    (hb : b ≠ 0) (hu : 0 < fp.u)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    exists (DeltaA D : Fin m -> Fin (m + k) -> Real),
      UndetRowwiseBackwardErrorFeasible m (m + k) A DeltaA b x_hat eta /\
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA i j) :
            Matrix (Fin m) (Fin m) Real) ≠ 0 /\
      (forall i j, DeltaA i j = eta * D i j) /\
      (forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i) /\
      ((fun j => x_hat j - x j) = fun j =>
        eta * higham21Eq21_11FirstOrder A D b j +
          higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D eta)) eta j) /\
      vecNorm2
          (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A D eta)) eta) <=
        eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /\
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
        ((m + k : Nat) : Real) * eta *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /
            vecNorm2 x := by
  dsimp only
  let x_hat : Fin (m + k) -> Real :=
    higham21Eq21_11ComputedQhat fp m k A b
  let Aplus : Fin (m + k) -> Fin m -> Real :=
    undetAplusOfGramNonsingInv A
  let x : Fin (m + k) -> Real := rectMatMulVec Aplus b
  let eta : Real := gamma fp (Higham21QMethodRoundedGammaIndex m k)
  have hindex : 0 < Higham21QMethodRoundedGammaIndex m k := by
    have hmk : 0 < m + k := Nat.add_pos_left hm k
    have hhouse : 0 < householderConstructApplyGammaIndex (m + k) := by
      simp [householderConstructApplyGammaIndex]
    have hcomputed : 0 < Higham21QMethodComputedGammaIndex m k := by
      unfold Higham21QMethodComputedGammaIndex
      have haction :
          0 < (m + k) * householderConstructApplyGammaIndex (m + k) :=
        Nat.mul_pos hmk hhouse
      omega
    have hbase : 0 < Higham21QMethodRoundedGammaBaseIndex m k := by
      unfold Higham21QMethodRoundedGammaBaseIndex
      omega
    unfold Higham21QMethodRoundedGammaIndex
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hmk) hbase
  have heta_pos : 0 < eta := by
    exact hu.trans_le (by
      simpa [eta] using u_le_gamma fp hindex hvalid)
  have heta_nonneg : 0 <= eta := heta_pos.le
  obtain ⟨DeltaA, hfeas, hdetDelta⟩ :=
    higham21_theorem21_4_computed_qhat_rank_stable_gamma
      fp A b hm hdomain hvalid hCondSmall
  let D : Fin m -> Fin (m + k) -> Real := fun i j => DeltaA i j / eta
  have hDeltaScale : forall i j, DeltaA i j = eta * D i j := by
    intro i j
    dsimp [D]
    field_simp [heta_pos.ne']
  have hDrow : forall i : Fin m, rectRowNorm2 D i <= rectRowNorm2 A i := by
    intro i
    have hnorm : rectRowNorm2 D i = eta⁻¹ * rectRowNorm2 DeltaA i := by
      calc
        rectRowNorm2 D i =
            vecNorm2 (fun j : Fin (m + k) => eta⁻¹ * DeltaA i j) := by
          unfold rectRowNorm2
          congr 1
          funext j
          simp [D, div_eq_mul_inv, mul_comm]
        _ = |eta⁻¹| * rectRowNorm2 DeltaA i :=
          vecNorm2_smul eta⁻¹ (fun j : Fin (m + k) => DeltaA i j)
        _ = eta⁻¹ * rectRowNorm2 DeltaA i := by
          rw [abs_of_pos (inv_pos.mpr heta_pos)]
    rw [hnorm]
    calc
      eta⁻¹ * rectRowNorm2 DeltaA i <=
          eta⁻¹ * (eta * rectRowNorm2 A i) :=
        mul_le_mul_of_nonneg_left (hfeas.row_bound i)
          (inv_nonneg.mpr heta_nonneg)
      _ = rectRowNorm2 A i := by field_simp [heta_pos.ne']
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + DeltaA i j
  have hscaledMatrix : higham21Eq21_7ScaledMatrix A D eta = B := by
    ext i j
    simp only [higham21Eq21_7ScaledMatrix, B]
    rw [hDeltaScale i j]
  have hdetA :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_qmethod_full_row_rank_gram_det_ne_zero hdomain
  have hdetScaled :
      Matrix.det
        (rectGram (higham21Eq21_7ScaledMatrix A D eta) :
          Matrix (Fin m) (Fin m) Real) ≠ 0 := by
    simpa [hscaledMatrix, B] using hdetDelta
  let Gt : Fin m -> Fin m -> Real :=
    undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D eta)
  have hxhatFormula :=
    higham21_lemma21_2_transpose_range_of_min_norm_and_perturbed_gram_det_ne_zero
      A DeltaA b x_hat hfeas.min_norm hdetDelta
  have hscaledRhs :
      higham21Eq21_7ScaledRhs b (0 : Fin m -> Real) eta = b := by
    funext i
    simp [higham21Eq21_7ScaledRhs]
  have hperturbed :
      higham21Eq21_7PerturbedSolution A D b (0 : Fin m -> Real) Gt eta =
        x_hat := by
    calc
      higham21Eq21_7PerturbedSolution A D b (0 : Fin m -> Real) Gt eta =
          rectMatMulVec (undetAplusOfGramInv B (undetGramNonsingInv B)) b := by
        simp [higham21Eq21_7PerturbedSolution, Gt, hscaledMatrix, hscaledRhs]
      _ = rectTransposeMulVec B (matMulVec m (undetGramNonsingInv B) b) :=
        rectMatMulVec_undetAplusOfGramInv B (undetGramNonsingInv B) b
      _ = x_hat := by simpa [B] using hxhatFormula.symm
  have hbase :
      higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) = x := by
    rfl
  have hfirst :
      higham21Eq21_11FirstOrder A D b =
        higham21Eq21_7FirstOrder A D b (0 : Fin m -> Real)
          (undetGramNonsingInv A) :=
    higham21_eq21_11_firstOrder_eq_eq21_7_firstOrder A D b hdetA
  have hexact :
      (fun j => x_hat j - x j) = fun j =>
        eta * higham21Eq21_11FirstOrder A D b j +
          higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A) Gt eta j := by
    have h := higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
      A D b (0 : Fin m -> Real) eta hdetA hdetScaled
    rw [hperturbed, hbase, <- hfirst] at h
    simpa [Gt] using h
  let beta : Real := frobNorm Gt
  have hbeta_nonneg : 0 <= beta := frobNorm_nonneg Gt
  have hremainder :
      vecNorm2
          (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
            (undetGramNonsingInv A) Gt eta) <=
        eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta := by
    have h := higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
      A D b (0 : Fin m -> Real) (undetGramNonsingInv A) Gt
      eta beta eta heta_nonneg hbeta_nonneg
      (by simp [abs_of_pos heta_pos]) (le_refl beta)
    simpa [higham21Eq21_11QuadraticCoefficient, beta, Gt,
      abs_of_pos heta_pos] using h
  have hfirstBound :
      vecNorm2 (higham21Eq21_11FirstOrder A D b) <=
        ((m + k : Nat) : Real) *
          higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [Aplus, x] using
      higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_of_card_le_one
        A D b hm (Nat.le_add_right m k) hscalar hdetA
          (by norm_num : (0 : Real) <= 1) (by simpa using hDrow)
  have habsolute :
      vecNorm2 (fun j => x_hat j - x j) <=
        ((m + k : Nat) : Real) * eta *
            higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta := by
    calc
      vecNorm2 (fun j => x_hat j - x j) =
          vecNorm2 (fun j =>
            eta * higham21Eq21_11FirstOrder A D b j +
              higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
                (undetGramNonsingInv A) Gt eta j) := congrArg vecNorm2 hexact
      _ <= vecNorm2 (fun j => eta * higham21Eq21_11FirstOrder A D b j) +
          vecNorm2
            (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
              (undetGramNonsingInv A) Gt eta) := vecNorm2_add_le _ _
      _ = eta * vecNorm2 (higham21Eq21_11FirstOrder A D b) +
          vecNorm2
            (higham21Eq21_7ExactRemainder A D b (0 : Fin m -> Real)
              (undetGramNonsingInv A) Gt eta) := by
        rw [vecNorm2_smul, abs_of_pos heta_pos]
      _ <= eta *
            (((m + k : Nat) : Real) *
              higham21Cond2With A Aplus * vecNorm2 x) +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta :=
        add_le_add (mul_le_mul_of_nonneg_left hfirstBound heta_nonneg) hremainder
      _ = ((m + k : Nat) : Real) * eta *
            higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta := by ring
  have hxmin : RectMinNormSolution m (m + k) A b x := by
    simpa [x, Aplus] using
      higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
        A b hdetA
  have hxne : x ≠ 0 := by
    intro hx0
    apply hb
    rw [<- hxmin.system_eq, hx0]
    ext i
    simp [rectMatMulVec]
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hxnorm
    apply hxne
    ext j
    exact (vecNorm2_eq_zero_iff x).mp hxnorm j
  have hxnorm_pos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  have hrelative :
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
        ((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /
            vecNorm2 x := by
    calc
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
          ((((m + k : Nat) : Real) * eta *
                higham21Cond2With A Aplus * vecNorm2 x) +
              eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta) /
            vecNorm2 x :=
        div_le_div_of_nonneg_right habsolute (le_of_lt hxnorm_pos)
      _ = ((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /
            vecNorm2 x := by
        field_simp [hxnorm_ne]
  refine ⟨DeltaA, D, hfeas, hdetDelta, hDeltaScale, hDrow, ?_, ?_, ?_⟩
  · simpa [Gt] using hexact
  · simpa [Gt] using hremainder
  · simpa [Aplus, x, eta] using hrelative

end NumStability
