-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The explicit quadratic remainder in equation (21.11).

import NumStability.Algorithms.Underdetermined.Higham21RankStability

namespace NumStability

set_option maxHeartbeats 1200000

/-- The explicit finite coefficient multiplying the squared perturbation
    radius in equation (21.11).  The normalized direction `D` is independent
    of the scalar radius; the final argument supplies the local neighborhood
    and the corresponding perturbed Gram inverse bound. -/
noncomputable def higham21Eq21_11QuadraticCoefficient {m n : Nat}
    (A D : Fin m -> Fin n -> Real) (b : Fin m -> Real) (eta : Real) : Real :=
  higham21Eq21_7FixedRadiusCoefficient A D b (0 : Fin m -> Real)
    (undetGramNonsingInv A) eta
    (frobNorm
      (undetGramNonsingInv (higham21Eq21_7ScaledMatrix A D eta)))

/-- The source-facing Q-method certificate can be chosen with a nonsingular
    perturbed Gram matrix.  This preserves the sharper perturbation produced
    before the final gamma enlargement and applies Theorem 21.1's rank
    stability argument to that same witness. -/
theorem higham21_theorem21_4_computed_qhat_rank_stable_gamma
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    ∃ DeltaA : Fin m -> Fin (m + k) -> Real,
      UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta /\
      Matrix.det
        (rectGram (fun i j => A i j + DeltaA i j) :
          Matrix (Fin m) (Fin m) Real) ≠ 0 := by
  dsimp only
  let Q_hat : Fin (m + k) -> Fin (m + k) -> Real :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m -> Fin m -> Real := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m -> Real := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) -> Real :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k -> Real))
  let eta0 : Real := Higham21QMethodRoundedRowwiseCoefficient fp m k
  let eta : Real := gamma fp (Higham21QMethodRoundedGammaIndex m k)
  let N := m + k
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  let Aplus : Fin (m + k) -> Fin m -> Real :=
    undetAplusOfGramNonsingInv A
  let cond := higham21Cond2With A Aplus
  have hComputed : gammaValid fp (Higham21QMethodComputedGammaIndex m k) :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hQsmall : Higham21QMethodQhatRadius fp m k < 1 :=
    Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid fp m k hm hvalid
  have heta0_nonneg : 0 <= eta0 :=
    Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hComputed
  have hetaBase : eta0 <= gamma fp H := by
    simpa [eta0, H] using
      Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base fp m k hm hvalid
  have hBaseValid : gammaValid fp H :=
    gammaValid_mono fp (by
      simpa [H] using Higham21QMethodRoundedGammaBaseIndex_le_index m k hm) hvalid
  have hN : 1 <= N := by simp [N]; omega
  have hfactor : 1 <= 3 * N := by omega
  have hscaled :
      ((3 * N : Nat) : Real) * gamma fp H <= eta := by
    simpa [eta, Higham21QMethodRoundedGammaIndex, N, H] using
      gamma_nsmul_le fp (3 * N) H hfactor hvalid
  have hscalar : 3 * eta0 * Real.sqrt (N : Real) <= eta := by
    calc
      3 * eta0 * Real.sqrt (N : Real) <=
          3 * gamma fp H * Real.sqrt (N : Real) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaBase (by norm_num))
          (Real.sqrt_nonneg _)
      _ <= 3 * gamma fp H * (N : Real) :=
        mul_le_mul_of_nonneg_left (higham21_sqrt_nat_le_nat N)
          (mul_nonneg (by norm_num) (gamma_nonneg fp hBaseValid))
      _ = ((3 * N : Nat) : Real) * gamma fp H := by
        push_cast
        ring
      _ <= eta := hscaled
  have hcond_nonneg : 0 <= cond :=
    higham21Cond2With_nonneg A Aplus
  have hCondActual :
      3 * (eta0 * Real.sqrt (N : Real) * cond) < 1 := by
    have hle :
        3 * (eta0 * Real.sqrt (N : Real) * cond) <= eta * cond := by
      calc
        3 * (eta0 * Real.sqrt (N : Real) * cond) =
            (3 * eta0 * Real.sqrt (N : Real)) * cond := by ring
        _ <= eta * cond := mul_le_mul_of_nonneg_right hscalar hcond_nonneg
    exact hle.trans_lt (by simpa [eta, cond, Aplus] using hCondSmall)
  have hraw :
      UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
        (Real.sqrt 2 * eta0) := by
    simpa [Q_hat, R_hat, y1, x_hat, eta0, N, cond, Aplus] using
      higham21_theorem21_4_computed_qhat_rowwise_backward_stable_of_cond2_smallness
        fp A b hm hdomain hComputed hQsmall hCondActual
  rcases hraw with ⟨DeltaA, hfeas0⟩
  have hcoeff : Real.sqrt 2 * eta0 <= eta := by
    simpa [eta0, eta] using
      Higham21QMethodRoundedOutputCoefficient_le_gamma_index fp m k hm hvalid
  have heta_nonneg : 0 <= eta := gamma_nonneg fp hvalid
  have hfeas :
      UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta :=
    { eta_nonneg := heta_nonneg
      min_norm := hfeas0.min_norm
      row_bound := fun i =>
        (hfeas0.row_bound i).trans
          (mul_le_mul_of_nonneg_right hcoeff (rectRowNorm2_nonneg A i)) }
  let c : Real :=
    (Real.sqrt 2 * eta0) * Real.sqrt (N : Real) * cond
  have hc_nonneg : 0 <= c := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) heta0_nonneg)
        (Real.sqrt_nonneg _)) hcond_nonneg
  have hsqrt_two_le_three : Real.sqrt 2 <= 3 := by
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : Real) := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : Real)]
  have hbase_nonneg :
      0 <= eta0 * Real.sqrt (N : Real) * cond :=
    mul_nonneg (mul_nonneg heta0_nonneg (Real.sqrt_nonneg _)) hcond_nonneg
  have hc_lt : c < 1 := by
    have hc_le : c <= 3 * (eta0 * Real.sqrt (N : Real) * cond) := by
      calc
        c = Real.sqrt 2 * (eta0 * Real.sqrt (N : Real) * cond) := by
          simp [c]
          ring
        _ <= 3 * (eta0 * Real.sqrt (N : Real) * cond) :=
          mul_le_mul_of_nonneg_right hsqrt_two_le_three hbase_nonneg
    exact hc_le.trans_lt hCondActual
  have hProduct :
      rectOpNorm2Le (rectMatMul Aplus DeltaA) c := by
    simpa [c, N, cond] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA Aplus (Real.sqrt 2 * eta0)
        (mul_nonneg (Real.sqrt_nonneg _) heta0_nonneg) hfeas0.row_bound
  have hdetA :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_qmethod_full_row_rank_gram_det_ne_zero hdomain
  have hdetPerturbed :
      Matrix.det
        (rectGram (fun i j => A i j + DeltaA i j) :
          Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_theorem21_1_perturbed_gram_det_ne_zero_of_gram_det_ne_zero
      A DeltaA hdetA (by simpa [Aplus] using hProduct) hc_nonneg hc_lt
  exact ⟨DeltaA, hfeas, hdetPerturbed⟩

/-- Higham, 2nd ed., Chapter 21, equation (21.11), with the printed
    `O(u^2)` term replaced by a finite, explicit `eta^2 * C` bound.

    The perturbation direction is normalized rowwise, so its size is
    independent of `eta`; the coefficient is the fixed-radius remainder
    coefficient from equation (21.7). -/
theorem higham21_eq21_11_computed_qhat_relative_forward_error_quadratic
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hk : 0 < k) (hb : b ≠ 0) (hu : 0 < fp.u)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    ∃ (DeltaA D : Fin m -> Fin (m + k) -> Real),
      UndetRowwiseBackwardErrorFeasible m (m + k)
          A DeltaA b x_hat eta /\
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
        (((m + k : Nat) : Real) * eta *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) +
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
    have hnorm :
        rectRowNorm2 D i = eta⁻¹ * rectRowNorm2 DeltaA i := by
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
        mul_le_mul_of_nonneg_left (hfeas.row_bound i) (inv_nonneg.mpr heta_nonneg)
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
    rw [hperturbed, hbase, ← hfirst] at h
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
  have hN : 2 <= m + k := by omega
  have hfirstBound :
      vecNorm2 (higham21Eq21_11FirstOrder A D b) <=
        ((m + k : Nat) : Real) *
          higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [Aplus, x] using
      higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
        A D b hN hdetA (by norm_num : (0 : Real) <= 1)
        (by simpa using hDrow)
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
    rw [← hxmin.system_eq, hx0]
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
        (((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus) +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /
            vecNorm2 x := by
    calc
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
          ((((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus *
                vecNorm2 x) +
              eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta) /
            vecNorm2 x :=
        div_le_div_of_nonneg_right habsolute (le_of_lt hxnorm_pos)
      _ = (((m + k : Nat) : Real) * eta * higham21Cond2With A Aplus) +
          eta ^ 2 * higham21Eq21_11QuadraticCoefficient A D b eta /
            vecNorm2 x := by
        field_simp [hxnorm_ne]
  refine ⟨DeltaA, D, hfeas, hdetDelta, hDeltaScale, hDrow, ?_, ?_, ?_⟩
  · simpa [Gt] using hexact
  · simpa [Gt] using hremainder
  · simpa [Aplus, x, eta] using hrelative

end NumStability
