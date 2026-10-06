import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.RoundedReplay.RoundedReplay
import NumStability.Algorithms.RankOneUpdate
import NumStability.Source.Higham.Chapter21.Section03.MethodComparison.Core
import NumStability.Source.Higham.Chapter21.Theorem04.ModifiedGramSchmidtQMethod.Core
import NumStability.Source.Higham.Chapter21.Corrections.CorrectedMGS.RoundedReplay
import NumStability.Source.Higham.Chapter21.Theorem04.ModifiedGramSchmidtQMethod.RoundedReplay
import NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError

/-!
# Algorithms.Underdetermined.Higham21MGSRounded

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, corrected MGS formation on printed page 413.





namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## A rounded corrected-MGS step -/













































































































































































































































/-! ## The backward loop and its repaired-action majorant -/




























































































































































































































/-! ## A rowwise action certificate for a fixed triangular-solve vector -/






private theorem higham21_vecNorm2_ne_zero_of_fun_ne_zero {m : Nat}
    {y : Fin m -> Real} (hy : y ≠ 0) : vecNorm2 y ≠ 0 := by
  intro hnorm
  exact hy (funext ((vecNorm2_eq_zero_iff y).mp hnorm))

private theorem higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero {m : Nat}
    {y : Fin m -> Real} (hy : y ≠ 0) : vecNorm2Sq y ≠ 0 := by
  intro hsq
  apply higham21_vecNorm2_ne_zero_of_fun_ne_zero hy
  unfold vecNorm2
  simp [hsq]

/-- The fixed-vector rank-one correction has exactly the requested action. -/
theorem higham21_mgs_fixedVectorActionCorrection_action {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) (hy : y ≠ 0) :
    rectMatMulVec (higham21MGSFixedVectorActionCorrection y e) y = e := by
  have hsq := higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero hy
  ext i
  unfold rectMatMulVec higham21MGSFixedVectorActionCorrection
  calc
    (Finset.univ.sum fun j : Fin m =>
        (1 / vecNorm2Sq y) * (e i * y j) * y j) =
        (1 / vecNorm2Sq y) * e i *
          (Finset.univ.sum fun j : Fin m => y j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (1 / vecNorm2Sq y) * e i * vecNorm2Sq y := rfl
    _ = e i := by field_simp [hsq]

/-- Exact row norm of the fixed-vector rank-one action correction. -/
theorem higham21_mgs_fixedVectorActionCorrection_rowNorm {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) (hy : y ≠ 0)
    (i : Fin n) :
    rectRowNorm2 (higham21MGSFixedVectorActionCorrection y e) i =
      |e i| / vecNorm2 y := by
  have hynorm := higham21_vecNorm2_ne_zero_of_fun_ne_zero hy
  have hsqNonneg : 0 <= vecNorm2Sq y := vecNorm2Sq_nonneg y
  have hsq : vecNorm2Sq y = vecNorm2 y ^ 2 := (vecNorm2_sq y).symm
  change
    vecNorm2 (fun j : Fin m => (1 / vecNorm2Sq y) * (e i * y j)) =
      |e i| / vecNorm2 y
  have hfun :
      (fun j : Fin m => (1 / vecNorm2Sq y) * (e i * y j)) =
        fun j => ((1 / vecNorm2Sq y) * e i) * y j := by
    funext j
    ring
  rw [hfun, vecNorm2_smul, abs_mul,
    abs_of_nonneg (one_div_nonneg.mpr hsqNonneg), hsq]
  field_simp [hynorm]

/-- Componentwise forward error becomes a rowwise perturbation of the action
matrix for the fixed nonzero vector `y`. -/
theorem higham21_fl_mgs_corrected_output_repaired_action_rowwise
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (hvalid : gammaValid fp (n + 3)) (hy : y ≠ 0) :
    exists DeltaQ : Fin n -> Fin m -> Real,
      higham21FlMGSCorrectedOutput fp Qhat y =
        rectMatMulVec (fun i j => Qrepair i j + DeltaQ i j) y /\
      (forall i,
        rectRowNorm2 DeltaQ i <=
          higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i /
            vecNorm2 y) := by
  let e : Fin n -> Real := fun i =>
    higham21FlMGSCorrectedOutput fp Qhat y i -
      higham21MGSNaiveFormation Qrepair y i
  let DeltaQ := higham21MGSFixedVectorActionCorrection y e
  have he : forall i,
      |e i| <= higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i := by
    intro i
    exact higham21_fl_mgs_corrected_output_repaired_action_componentwise
      fp Qhat Qrepair y hvalid i
  have hyPos : 0 < vecNorm2 y :=
    lt_of_le_of_ne (vecNorm2_nonneg y)
      (Ne.symm (higham21_vecNorm2_ne_zero_of_fun_ne_zero hy))
  refine ⟨DeltaQ, ?_, ?_⟩
  . have hDelta := higham21_mgs_fixedVectorActionCorrection_action y e hy
    ext i
    have haction := congrFun
      (rectMatMulVec_mat_add Qrepair DeltaQ y) i
    rw [hDelta] at haction
    have heq :
        rectMatMulVec (fun r c => Qrepair r c + DeltaQ r c) y i =
          higham21MGSNaiveFormation Qrepair y i + e i := by
      simpa [higham21MGSNaiveFormation] using haction
    rw [heq]
    simp [e]
  . intro i
    rw [higham21_mgs_fixedVectorActionCorrection_rowNorm y e hy i]
    exact (div_le_div_iff_of_pos_right hyPos).2 (he i)

/-! ## Explicit rank-one system corrections -/









/-- The feasibility correction makes the corrected system solve exactly. -/
theorem higham21_mgs_feasibilityCorrection_solves {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) (hx : x ≠ 0) :
    rectMatMulVec
      (fun i j => B i j + higham21MGSFeasibilityCorrection B b x i j) x =
        b := by
  let e : Fin m -> Real := fun i => b i - rectMatMulVec B x i
  have hcorr := higham21_mgs_fixedVectorActionCorrection_action x e hx
  calc
    rectMatMulVec
        (fun i j => B i j + higham21MGSFeasibilityCorrection B b x i j) x =
        fun i => rectMatMulVec B x i +
          rectMatMulVec (higham21MGSFeasibilityCorrection B b x) x i :=
      rectMatMulVec_mat_add B (higham21MGSFeasibilityCorrection B b x) x
    _ = fun i => rectMatMulVec B x i + e i := by
      rw [show higham21MGSFeasibilityCorrection B b x =
          higham21MGSFixedVectorActionCorrection x e by
        rfl, hcorr]
    _ = b := by
      funext i
      simp [e]

/-- Exact row norm of the feasibility correction. -/
theorem higham21_mgs_feasibilityCorrection_rowNorm {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) (hx : x ≠ 0) (i : Fin m) :
    rectRowNorm2 (higham21MGSFeasibilityCorrection B b x) i =
      |b i - rectMatMulVec B x i| / vecNorm2 x := by
  simpa [higham21MGSFeasibilityCorrection] using
    higham21_mgs_fixedVectorActionCorrection_rowNorm x
      (fun r => b r - rectMatMulVec B x r) hx i










/-- The transpose action of the range correction is the exact range
residual. -/
theorem higham21_mgs_rangeCorrection_action {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (hz : z ≠ 0) :
    rectTransposeMulVec (higham21MGSRangeCorrection B x z) z =
      fun j => x j - rectTransposeMulVec B z j := by
  let e : Fin n -> Real := fun j => x j - rectTransposeMulVec B z j
  have hcorr := higham21_mgs_fixedVectorActionCorrection_action z e hz
  ext j
  have hj := congrFun hcorr j
  simpa [higham21MGSRangeCorrection, e, rectTransposeMulVec,
    rectMatMulVec, finiteTranspose] using hj

/-- Adding the range correction makes the transpose representation exact. -/
theorem higham21_mgs_rangeCorrection_represents {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (hz : z ≠ 0) :
    rectTransposeMulVec
      (fun i j => B i j + higham21MGSRangeCorrection B x z i j) z = x := by
  have hcorr := higham21_mgs_rangeCorrection_action B x z hz
  ext j
  have hj := congrFun hcorr j
  unfold rectTransposeMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  change rectTransposeMulVec B z j +
      rectTransposeMulVec (higham21MGSRangeCorrection B x z) z j = x j
  rw [hj]
  ring





















/-! ## The Problem 19.12 repair and the triangular-solve perturbation -/




















































































































































































/-! ## Actual-output Theorem 21.4 handoff -/





























/-- Build the Lemma 21.2 transfer from the explicit rank-one feasibility and
transpose-range corrections.  The remaining numerical obligations are now
only the two displayed row bounds (and nonzero `x`/`z`). -/
noncomputable def Higham21MGSRoundedSystemTransfer.of_rankOneCorrections
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real) (etaAction : Real)
    (z : Fin m -> Real)
    (hx : higham21FlMGSCorrectedOutput fp Qhat y ≠ 0)
    (hz : z ≠ 0)
    (heta : 0 <= etaAction)
    (hrow1 : forall i,
      rectRowNorm2
        (higham21MGSFeasibilityCorrection
          (fun r c => A r c + DeltaBase r c) b
          (higham21FlMGSCorrectedOutput fp Qhat y)) i <=
        etaAction * rectRowNorm2 A i)
    (hrow2 : forall i,
      rectRowNorm2
        (higham21MGSRangeCorrection
          (fun r c => A r c + DeltaBase r c)
          (higham21FlMGSCorrectedOutput fp Qhat y) z) i <=
        etaAction * rectRowNorm2 A i) :
    Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction := by
  let B : Fin m -> Fin n -> Real :=
    fun r c => A r c + DeltaBase r c
  let x : Fin n -> Real := higham21FlMGSCorrectedOutput fp Qhat y
  let DeltaA1 := higham21MGSFeasibilityCorrection B b x
  let DeltaA2 := higham21MGSRangeCorrection B x z
  refine
    { DeltaA1 := DeltaA1
      DeltaA2 := DeltaA2
      dual := z
      first_system := ?_
      second_system := ?_
      row_bound1 := ?_
      row_bound2 := ?_
      eta_nonneg := heta }
  . simpa [B, x, DeltaA1, add_assoc] using
      higham21_mgs_feasibilityCorrection_solves B b x hx
  . simpa [B, x, DeltaA2, add_assoc] using
      (higham21_mgs_rangeCorrection_represents B x z hz).symm
  . simpa [B, x, DeltaA1] using hrow1
  . simpa [B, x, DeltaA2] using hrow2

/-- Actual rounded-output rowwise theorem.  This is the economy-MGS form of
the Lemma 21.2 handoff used in Theorem 21.4. -/
theorem higham21_mgs_rounded_actual_output_rowwise_backward_stable
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real)
    {etaBase etaAction : Real}
    (hetaBase : 0 <= etaBase)
    (hbase : forall i,
      rectRowNorm2 DeltaBase i <= etaBase * rectRowNorm2 A i)
    (htransfer : Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * ((etaBase + etaAction) * Real.sqrt (n : Real) *
        higham21Cond2With A Aplus) < 1) :
    UndetRowwiseBackwardErrorBounded m n A b
      (higham21FlMGSCorrectedOutput fp Qhat y)
      (Real.sqrt 2 * (etaBase + etaAction)) := by
  let Delta1 : Fin m -> Fin n -> Real :=
    fun i j => DeltaBase i j + htransfer.DeltaA1 i j
  let Delta2 : Fin m -> Fin n -> Real :=
    fun i j => DeltaBase i j + htransfer.DeltaA2 i j
  let eta := etaBase + etaAction
  let rho := eta * Real.sqrt (n : Real) * higham21Cond2With A Aplus
  have heta : 0 <= eta := add_nonneg hetaBase htransfer.eta_nonneg
  have hrow1 : forall i,
      rectRowNorm2 Delta1 i <= eta * rectRowNorm2 A i := by
    intro i
    simpa [Delta1, eta] using
      higham21_rectRowNorm2_add_le_of_row_bounds
        DeltaBase htransfer.DeltaA1 A hbase htransfer.row_bound1 i
  have hrow2 : forall i,
      rectRowNorm2 Delta2 i <= eta * rectRowNorm2 A i := by
    intro i
    simpa [Delta2, eta] using
      higham21_rectRowNorm2_add_le_of_row_bounds
        DeltaBase htransfer.DeltaA2 A hbase htransfer.row_bound2 i
  have hfirst :
      rectMatMulVec (fun i j => A i j + Delta1 i j)
        (higham21FlMGSCorrectedOutput fp Qhat y) = b := by
    simpa [Delta1, add_assoc] using htransfer.first_system
  have hsecond :
      higham21FlMGSCorrectedOutput fp Qhat y =
        rectTransposeMulVec (fun i j => A i j + Delta2 i j)
          htransfer.dual := by
    simpa [Delta2, add_assoc] using htransfer.second_system
  have hprod1 : rectOpNorm2Le (rectMatMul Aplus Delta1) rho := by
    simpa [rho, eta] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A Delta1 Aplus eta heta hrow1
  have hprod2 : rectOpNorm2Le (rectMatMul Aplus Delta2) rho := by
    simpa [rho, eta] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A Delta2 Aplus eta heta hrow2
  apply higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
    A Aplus Delta1 Delta2 b
      (higham21FlMGSCorrectedOutput fp Qhat y) htransfer.dual
      rho rho eta hRight hfirst hsecond hprod1 hprod2
  . simpa [rho, eta] using hsmall
  . exact heta
  . exact hrow1
  . exact hrow2

/-- Printed `omega^R` consequence for the actual rounded recurrence output. -/
theorem higham21_mgs_rounded_actual_output_omegaR_le
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real)
    {etaBase etaAction : Real}
    (hetaBase : 0 <= etaBase)
    (hbase : forall i,
      rectRowNorm2 DeltaBase i <= etaBase * rectRowNorm2 A i)
    (htransfer : Higham21MGSRoundedSystemTransfer
      fp A b Qhat y DeltaBase etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * ((etaBase + etaAction) * Real.sqrt (n : Real) *
        higham21Cond2With A Aplus) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
      (higham21FlMGSCorrectedOutput fp Qhat y) <=
        Real.sqrt 2 * (etaBase + etaAction) := by
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
    (higham21_mgs_rounded_actual_output_rowwise_backward_stable
      fp A b Qhat y DeltaBase hetaBase hbase htransfer Aplus hRight hsmall)
























/-- Theorem-21.4-level actual-output result with the computed triangular solve
folded into the repaired `R` factor.  The recurrence-specific remaining
hypothesis is `Higham21MGSRoundedActionToSystemTransfer`; the explicit
rank-one constructor above reduces it to row bounds and nonzero branches. -/
theorem higham21_mgs_rounded_forwardSub_actual_output_theorem21_4
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat Qrepair : Fin n -> Fin m -> Real)
    (Rhat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    {etaQR etaAction : Real}
    (hrepair : Higham21MGSSelectedRepair
      A Rhat Qrepair DeltaAT etaQR)
    (hdiag : forall i : Fin m, Rhat i i ≠ 0)
    (hvalidStep : gammaValid fp (n + 3))
    (hvalidSolve : gammaValid fp m)
    (htransfer : Higham21MGSRoundedActionToSystemTransfer
      fp A b Qhat Qrepair Rhat DeltaAT
        (fl_forwardSub fp m (matTranspose Rhat) b) etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * (((etaQR + gamma fp m * (1 + etaQR)) + etaAction) *
        Real.sqrt (n : Real) * higham21Cond2With A Aplus) < 1) :
    exists DeltaR : Fin m -> Fin m -> Real,
      (forall i j, |DeltaR i j| <= gamma fp m * |Rhat i j|) /\
      (forall i,
        matMulVec m (matTranspose (fun a b => Rhat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose Rhat) b) i = b i) /\
      (forall i j,
        finiteTranspose A i j +
            higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR i j =
          matMulRect n m m Qrepair
            (fun a b => Rhat a b + DeltaR a b) i j) /\
      UndetRowwiseBackwardErrorBounded m n A b
        (higham21FlMGSCorrectedOutput fp Qhat
          (fl_forwardSub fp m (matTranspose Rhat) b))
        (Real.sqrt 2 *
          ((etaQR + gamma fp m * (1 + etaQR)) + etaAction)) := by
  let y := fl_forwardSub fp m (matTranspose Rhat) b
  let etaBase := etaQR + gamma fp m * (1 + etaQR)
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m Rhat b hdiag hrepair.upper hvalidSolve
  have hgamma : 0 <= gamma fp m := gamma_nonneg fp hvalidSolve
  have hetaBase : 0 <= etaBase := by
    exact add_nonneg hrepair.eta_nonneg
      (mul_nonneg hgamma (add_nonneg zero_le_one hrepair.eta_nonneg))
  have hfoldFactor := higham21_mgs_folded_deltaAT_factor
    (finiteTranspose A) DeltaAT Qrepair Rhat DeltaR hrepair.factor
  have hfoldColumn := higham21_mgs_folded_deltaAT_column_bound
    (finiteTranspose A) DeltaAT Qrepair Rhat DeltaR
      hrepair.orthonormal hrepair.factor hrepair.eta_nonneg
      hrepair.column_bound hgamma hDeltaR
  have hbase : forall i,
      rectRowNorm2
        (finiteTranspose
          (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR)) i <=
        etaBase * rectRowNorm2 A i := by
    have hrows := higham21_row_bounds_of_transposed_qr_column_bounds
      (finiteTranspose A)
      (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) hfoldColumn
    intro i
    simpa [etaBase] using hrows i
  have hcomparison : forall i,
      |higham21FlMGSCorrectedOutput fp Qhat y i -
          higham21MGSNaiveFormation Qrepair y i| <=
        higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i :=
    higham21_fl_mgs_corrected_output_repaired_action_componentwise
      fp Qhat Qrepair y hvalidStep
  have hsystem := htransfer DeltaR hDeltaR (by simpa [y] using hsolve)
    hcomparison
  have hrowwise :=
    higham21_mgs_rounded_actual_output_rowwise_backward_stable
      fp A b Qhat y
      (finiteTranspose
        (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR))
      hetaBase hbase hsystem Aplus hRight (by simpa [etaBase] using hsmall)
  refine ⟨DeltaR, hDeltaR, hsolve, ?_, ?_⟩
  . exact hfoldFactor
  . simpa [y, etaBase] using hrowwise

/-- `omega^R` form of the folded actual-output theorem. -/
theorem higham21_mgs_rounded_forwardSub_actual_output_omegaR_le
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat Qrepair : Fin n -> Fin m -> Real)
    (Rhat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    {etaQR etaAction : Real}
    (hrepair : Higham21MGSSelectedRepair
      A Rhat Qrepair DeltaAT etaQR)
    (hdiag : forall i : Fin m, Rhat i i ≠ 0)
    (hvalidStep : gammaValid fp (n + 3))
    (hvalidSolve : gammaValid fp m)
    (htransfer : Higham21MGSRoundedActionToSystemTransfer
      fp A b Qhat Qrepair Rhat DeltaAT
        (fl_forwardSub fp m (matTranspose Rhat) b) etaAction)
    (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hsmall :
      3 * (((etaQR + gamma fp m * (1 + etaQR)) + etaAction) *
        Real.sqrt (n : Real) * higham21Cond2With A Aplus) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
      (higham21FlMGSCorrectedOutput fp Qhat
        (fl_forwardSub fp m (matTranspose Rhat) b)) <=
      Real.sqrt 2 *
        ((etaQR + gamma fp m * (1 + etaQR)) + etaAction) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hfactor, hrowwise⟩ :=
    higham21_mgs_rounded_forwardSub_actual_output_theorem21_4
      fp A b Qhat Qrepair Rhat DeltaAT hrepair hdiag hvalidStep
        hvalidSolve htransfer Aplus hRight hsmall
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate hrowwise

end

end NumStability
