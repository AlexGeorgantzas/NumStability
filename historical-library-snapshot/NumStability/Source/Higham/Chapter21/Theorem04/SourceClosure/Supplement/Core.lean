import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.EndToEnd.Core
import NumStability.Source.Higham.Chapter21.Equation03.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation04.QRFoundations
import NumStability.Source.Higham.Chapter21.Theorem04.SourceClosure.SourceClosure

/-!
# Algorithms.Underdetermined.Higham21Theorem214SourceClosure

Historical W04 compatibility facade retaining the exact private reverse closure.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Strict source closure for Theorem 21.4 and the Q-method output in (21.11).





namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
The printed Theorem 21.4 assumes full row rank and a condition of the form
`cond₂(A) m n γₙ < 1`; it does not assume that a computed triangular factor
has nonzero diagonal.  The older concrete endpoints exposed that operational
fact as an additional domain field.  This file derives it from the already
proved QR row perturbation and the printed small-condition hypothesis.

For the retained-trace Givens route, the same source closure also absorbs the
separate `Q_hat` replay-radius premise into one explicit schedule gamma index.
-/



















































































































































































































/-- Theorem 21.4 on the actual rounded Householder output, now with exactly
the printed rank/small-condition source surface (plus model gamma validity). -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_source
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m -> Fin m -> Real := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k -> Real))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (gamma fp (Higham21QMethodRoundedGammaIndex m k)) := by
  exact higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
    fp A b hm
      (Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness
        fp A hm hfull hvalid hCondSmall)
      hvalid hCondSmall

/-! ## Retained-trace Givens replay smallness -/




















































































































































































































/-- The Givens alternative of Theorem 21.4 with all operational guards
derived from source rank, one schedule gamma-validity hypothesis, and the
printed small-condition inequality. -/
theorem higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hvalid : gammaValid fp (Higham21GivensOperationalGammaIndex m k))
    (hCondSmall :
      3 * (Higham21GivensActualRoundedRowwiseCoefficient fp m k *
        Real.sqrt (((m + k : Nat) : Real)) *
        higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensActualRoundedOutput fp m k A b (by
        exact Higham21GivensOperationalGammaIndex.valid8
          fp m k hm hvalid))
      (Real.sqrt 2 *
        Higham21GivensActualRoundedRowwiseCoefficient fp m k) := by
  have hvalid8 : gammaValid fp 8 :=
    Higham21GivensOperationalGammaIndex.valid8 fp m k hm hvalid
  have hvalidM : gammaValid fp m :=
    Higham21GivensOperationalGammaIndex.validM fp m k hm hvalid
  have hdiag :=
    higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness
      fp A hm hfull hvalid hCondSmall
  have hgram : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hQsmall :=
    Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid
      fp m k hm hvalid
  simpa using
    higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable
      fp A b hm hvalid8 hdiag hvalidM hgram hQsmall hCondSmall

end NumStability
