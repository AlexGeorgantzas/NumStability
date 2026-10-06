-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Theorem 21.4 through the concrete staged Givens QR factorization of A^T.

import NumStability.Algorithms.Underdetermined.Higham21RowwiseMeasure

namespace NumStability

/-- The Chapter 19 Givens and Householder source contracts have identical
    algebraic fields.  This lossless adapter exposes a Givens certificate to
    the method-independent QR-to-Q-method handoff in `UnderdeterminedSolve`.

    The target type retains its historical Householder name, but this theorem
    uses no Householder-specific fact. -/
theorem higham21_givens_qr_backward_error_to_generic_certificate
    {rows cols : Nat}
    {A : Fin rows -> Fin cols -> Real}
    {Q : Fin rows -> Fin rows -> Real}
    {R_hat : Fin rows -> Fin cols -> Real}
    {etaQR : Real}
    (hqr : H19.Theorem19_10.GivensQRBackwardError
      rows cols A Q R_hat etaQR) :
    H19.Theorem19_4.HouseholderQRBackwardError
      rows cols A Q R_hat etaQR := by
  exact
    { upper := hqr.upper
      orth := hqr.orth
      result := hqr.result }

/-- Method-independent Theorem 21.4 handoff specialized to a supplied Givens
    QR certificate for `A^T`.  The top-block diagonal condition is exactly the
    nonbreakdown condition needed by the rounded triangular solve. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_givens_qr_transpose_certificate
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (b : Fin m -> Real)
    {etaQR : Real} (hetaQR : 0 <= etaQR)
    (hqr : H19.Theorem19_10.GivensQRBackwardError (m + k) m
      (finiteTranspose A) Q R_tall etaQR)
    (hdiag : forall i : Fin m,
      Not (R_tall (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hvalidTri2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k) Q
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose (fun i j => R_tall (Fin.castAdd k i) j)) b)
          (0 : Fin k -> Real)))
      (etaQR + gamma fp m * (1 + etaQR)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_qr_transpose_certificate
      fp A Q R_tall b hetaQR
      (higham21_givens_qr_backward_error_to_generic_certificate hqr)
      hdiag hvalidTri hvalidTri2

/-- The conservative staged Givens coefficient is nonnegative under the
    coefficient-kernel validity hypothesis used by Theorem 19.10. -/
theorem higham21_givens_qr_gamma_tilde_nonneg
    (fp : FPModel) (rows cols : Nat)
    (hvalidGivens : gammaValid fp 8) :
    0 <= H19.Theorem19_10.gamma_tilde fp rows cols := by
  have hbase :
      0 <= gamma fp 8 * Real.sqrt (rows : Real) :=
    mul_nonneg (gamma_nonneg fp hvalidGivens) (Real.sqrt_nonneg _)
  have hstage :
      0 <= residualAccumBound
        (gamma fp 8 * Real.sqrt (rows : Real))
        (givensQRStageTaskList rows cols
          (givensQRStageCount rows cols)).length :=
    residualAccumBound_nonneg _ hbase _
  have htotal :
      0 <= residualAccumBound
        (residualAccumBound
          (gamma fp 8 * Real.sqrt (rows : Real))
          (givensQRStageTaskList rows cols
            (givensQRStageCount rows cols)).length)
        (givensQRStageCount rows cols) :=
    residualAccumBound_nonneg _ hstage _
  simpa [H19.Theorem19_10.gamma_tilde] using htotal

/-- Exact orthogonal witness attached to the concrete staged Givens QR
    backward-error certificate for `A^T`.

    This is a proof-selected exact factor, not a rounded formed-`Q` matrix. -/
noncomputable def higham21GivensQMethodQ
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (hvalidGivens : gammaValid fp 8) :
    Fin (m + k) -> Fin (m + k) -> Real :=
  Classical.choose
    (fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
      fp (m + k) m (finiteTranspose A)
      (givensQRStageCount (m + k) m) hvalidGivens)

/-- Concrete upper-trapezoidal output of staged Givens QR applied to `A^T`. -/
noncomputable def higham21GivensQMethodRTall
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fl_givensQRStageFold fp (m + k) m
    (givensQRStageCount (m + k) m) (finiteTranspose A)

/-- Q-method vector obtained from the computed staged Givens `R_hat`, the
    rounded triangular solve, and the exact orthogonal certificate witness.

    A future fully rounded Givens endpoint should replace the final exact
    matrix-vector action by a stored-rotation application and prove its own
    action-error certificate. -/
noncomputable def higham21GivensQMethodOutput
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (b : Fin m -> Real)
    (hvalidGivens : gammaValid fp 8) :
    Fin (m + k) -> Real :=
  let R_top : Fin m -> Fin m -> Real := fun i j =>
    higham21GivensQMethodRTall fp m k A (Fin.castAdd k i) j
  matMulVec (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens)
    (Fin.append
      (fl_forwardSub fp m (matTranspose R_top) b)
      (0 : Fin k -> Real))

/-- Proved row-wise coefficient for the exact-witness Givens Q-method path:
    the staged Givens QR coefficient, the triangular-solve coefficient, and
    their product term. -/
noncomputable def Higham21GivensQMethodRowwiseCoefficient
    (fp : FPModel) (m k : Nat) : Real :=
  H19.Theorem19_10.gamma_tilde fp (m + k) m +
    gamma fp m *
      (1 + H19.Theorem19_10.gamma_tilde fp (m + k) m)

/-- The concrete staged factorization of `A^T` supplies the Givens certificate
    consumed by the Chapter 21 adapter. -/
theorem higham21_givens_qr_transpose_certificate
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8) :
    H19.Theorem19_10.GivensQRBackwardError (m + k) m
      (finiteTranspose A)
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      (higham21GivensQMethodRTall fp m k A)
      (H19.Theorem19_10.gamma_tilde fp (m + k) m) := by
  simpa [higham21GivensQMethodQ, higham21GivensQMethodRTall] using
    (H19.Theorem19_10.givens_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm
      (Nat.le_add_right m k) hvalidGivens)

/-- Nonnegativity of the complete Givens Q-method row-wise coefficient. -/
theorem Higham21GivensQMethodRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : Nat)
    (hvalidGivens : gammaValid fp 8)
    (hvalidTri : gammaValid fp m) :
    0 <= Higham21GivensQMethodRowwiseCoefficient fp m k := by
  have hQR :
      0 <= H19.Theorem19_10.gamma_tilde fp (m + k) m :=
    higham21_givens_qr_gamma_tilde_nonneg fp (m + k) m hvalidGivens
  have hTri : 0 <= gamma fp m := gamma_nonneg fp hvalidTri
  unfold Higham21GivensQMethodRowwiseCoefficient
  exact add_nonneg hQR
    (mul_nonneg hTri (add_nonneg zero_le_one hQR))

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: row-wise backward stability of
    the Q method instantiated with concrete staged Givens QR on `A^T`.

    All implementation-side conditions remain visible: positivity of the row
    dimension, Givens kernel validity, computed top-block nonbreakdown, and the
    two triangular-solve gamma-validity conditions.  The output uses the exact
    orthogonal witness attached to the computed factorization certificate. -/
theorem higham21_theorem21_4_givens_q_method_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensQMethodRTall fp m k A
        (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hvalidTri2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensQMethodOutput fp m k A b hvalidGivens)
      (Higham21GivensQMethodRowwiseCoefficient fp m k) := by
  simpa [higham21GivensQMethodOutput,
      Higham21GivensQMethodRowwiseCoefficient] using
    (higham21_theorem21_4_q_method_rowwise_backward_stable_of_givens_qr_transpose_certificate
      fp A
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      (higham21GivensQMethodRTall fp m k A)
      b
      (higham21_givens_qr_gamma_tilde_nonneg
        fp (m + k) m hvalidGivens)
      (higham21_givens_qr_transpose_certificate
        fp A hm hvalidGivens)
      hdiag hvalidTri hvalidTri2)

/-- Printed `omega^R` consequence of the concrete Givens row-wise
    certificate.  The right-hand-side perturbation is zero, as in Theorem 21.4. -/
theorem higham21_theorem21_4_givens_q_method_omegaR_le
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensQMethodRTall fp m k A
        (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hvalidTri2 : gammaValid fp (2 * m)) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensQMethodOutput fp m k A b hvalidGivens) <=
      Higham21GivensQMethodRowwiseCoefficient fp m k := by
  exact
    higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
      (higham21_theorem21_4_givens_q_method_rowwise_backward_stable
        fp A b hm hvalidGivens hdiag hvalidTri hvalidTri2)

end NumStability
