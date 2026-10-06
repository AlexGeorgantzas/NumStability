import NumStability.Algorithms.QR.HouseholderQRSupport

/-!
# Higham Lemma 19.3: actual rectangular stored-loop producers

The source-numbered rectangular wrapper historically asked callers to prove
the matrix-column and RHS component-budget inequalities for every step.  The
compact kernels already define deterministic relative budgets that prove
those inequalities.  This file connects those producers to the common-`Q`
sequence theorem and gives the standard single-`gamma` collapse.
-/

namespace NumStability

open scoped BigOperators

noncomputable section

/-- Actual stored-Householder sequence form of Lemma 19.3 with every local
matrix/RHS budget produced by the deterministic compact sequence budget. -/
theorem higham19_lemma19_3_actual_stored_sequence_backward_error
    {m n : Nat} (fp : FPModel) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (b_hat : Nat -> Fin m -> Real)
    (alpha : Nat -> Real)
    (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : forall k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : forall k (hk : k < n),
      (Finset.univ.sum fun i : Fin m =>
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0) :
    let c := storedQRCompactSequenceRelativeBudget
      hmn fp A_hat b_hat alpha
    exists (Q : Fin m -> Fin m -> Real)
        (dA : Fin m -> Fin n -> Real) (db : Fin m -> Real),
      IsOrthogonal m Q /\
      (forall i j, A_hat n i j =
        matMulRectLeft (matTranspose Q) (fun a col => A a col + dA a col) i j) /\
      (forall i, b_hat n i =
        matMulVec m (matTranspose Q) (fun a => b a + db a) i) /\
      (forall j : Fin n,
        vecNorm2 (fun i => dA i j) <=
          ((1 + c) ^ n - 1) * vecNorm2 (fun i => A i j)) /\
      vecNorm2 db <= ((1 + c) ^ n - 1) * vecNorm2 b := by
  let c := storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
  have hc : 0 <= c := by
    simpa [c] using
      storedQRCompactSequenceRelativeBudget_nonneg
        hmn fp A_hat b_hat alpha hm
  exact fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric
    fp hmn A b A_hat b_hat alpha c hc hm
    hInitA hInitb hStepA hStepb halpha hden
    (fun k hk j => by
      simpa [c] using
        storedQRCompactSequenceRelativeBudget_column_bound
          hmn fp A_hat b_hat alpha hm k hk j)
    (fun k hk => by
      simpa [c] using
        storedQRCompactSequenceRelativeBudget_rhs_bound
          hmn fp A_hat b_hat alpha hm k hk)

/-- Fully produced and collapsed Lemma 19.3 endpoint.  A nonzero signed-stage
denominator and the explicit compact-kernel operation count produce the local
budgets; the geometric accumulation is then compressed to
`gamma fp (n * stepOps)`. -/
theorem higham19_lemma19_3_actual_stored_sequence_gamma_bound_of_sourceDen_stepOps
    {m n stepOps : Nat} (fp : FPModel) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (b_hat : Nat -> Fin m -> Real)
    (alpha : Nat -> Real)
    (hn : 0 < n)
    (hm : gammaValid fp m)
    (hgamma : gammaValid fp (n * stepOps))
    (hstepOps : 31 * (n + 1) * m <= stepOps)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : forall k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : forall k (hk : k < n),
      (Finset.univ.sum fun i : Fin m =>
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0) :
    exists (Q : Fin m -> Fin m -> Real)
        (dA : Fin m -> Fin n -> Real) (db : Fin m -> Real),
      IsOrthogonal m Q /\
      (forall i j, A_hat n i j =
        matMulRectLeft (matTranspose Q) (fun a col => A a col + dA a col) i j) /\
      (forall i, b_hat n i =
        matMulVec m (matTranspose Q) (fun a => b a + db a) i) /\
      (forall j : Fin n,
        vecNorm2 (fun i => dA i j) <=
          gamma fp (n * stepOps) * vecNorm2 (fun i => A i j)) /\
      vecNorm2 db <= gamma fp (n * stepOps) * vecNorm2 b := by
  let c := gamma fp stepOps
  have hstep_le : stepOps <= n * stepOps := by
    simpa [one_mul] using Nat.mul_le_mul_right stepOps (Nat.succ_le_of_lt hn)
  have hgammaStep : gammaValid fp stepOps :=
    gammaValid_mono fp hstep_le hgamma
  have hc : 0 <= c := by
    simpa [c] using gamma_nonneg fp hgammaStep
  have hlocal : forall k : Fin n,
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k <= c := by
    intro k
    simpa [c] using
      storedQRCompactStepRelativeBudget_le_gamma_of_source_den_ne_zero_operation_count
        hmn fp A_hat b_hat alpha hm hgammaStep hstepOps k
        (by simpa using hden k.val k.isLt)
  rcases
    fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric
      fp hmn A b A_hat b_hat alpha c hc hm
      hInitA hInitb hStepA hStepb halpha hden
      (fun k hk j => by
        let kf : Fin n := ⟨k, hk⟩
        let cLocal := storedQRCompactStepRelativeBudget
          hmn fp A_hat b_hat alpha kf
        have hbudget :=
          householderCompactPanelRelativeBudget_stored_column_bound
            fp m n k
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (A_hat k) (b_hat k) hm j
        have hbudget' :
            vecNorm2 (fun i : Fin m =>
              if j.val < k then 0
              else householderCompactComponentBudget fp m
                (householderTrailingActiveVector m
                  ⟨k, lt_of_lt_of_le hk hmn⟩
                  (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
                (householderBetaSpec m
                  (householderTrailingActiveVector m
                    ⟨k, lt_of_lt_of_le hk hmn⟩
                    (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
                (fun a => A_hat k a j) i) <=
              cLocal * vecNorm2 (fun i : Fin m => A_hat k i j) := by
          simpa [cLocal, storedQRCompactStepRelativeBudget, kf] using hbudget
        exact hbudget'.trans
          (mul_le_mul_of_nonneg_right (by simpa [cLocal] using hlocal kf)
            (vecNorm2_nonneg (fun i : Fin m => A_hat k i j))))
      (fun k hk => by
        let kf : Fin n := ⟨k, hk⟩
        let cLocal := storedQRCompactStepRelativeBudget
          hmn fp A_hat b_hat alpha kf
        have hbudget :=
          householderCompactPanelRelativeBudget_stored_rhs_bound
            fp m n k
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (A_hat k) (b_hat k) hm
        have hbudget' :
            vecNorm2 (fun i : Fin m =>
              if i.val < k then 0
              else householderCompactComponentBudget fp m
                (householderTrailingActiveVector m
                  ⟨k, lt_of_lt_of_le hk hmn⟩
                  (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
                (householderBetaSpec m
                  (householderTrailingActiveVector m
                    ⟨k, lt_of_lt_of_le hk hmn⟩
                    (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
                (b_hat k) i) <= cLocal * vecNorm2 (b_hat k) := by
          simpa [cLocal, storedQRCompactStepRelativeBudget, kf] using hbudget
        exact hbudget'.trans
          (mul_le_mul_of_nonneg_right (by simpa [cLocal] using hlocal kf)
            (vecNorm2_nonneg (b_hat k)))) with
      ⟨Q, dA, db, hQ, hArep, hbrep, hdA, hdb⟩
  have hcollapse : (1 + c) ^ n - 1 <= gamma fp (n * stepOps) :=
    one_add_pow_sub_one_le_gamma_mul_of_le_gamma
      fp n stepOps hc (by simp [c]) hgamma
  refine ⟨Q, dA, db, hQ, hArep, hbrep, ?_, ?_⟩
  · intro j
    exact (hdA j).trans
      (mul_le_mul_of_nonneg_right hcollapse
        (vecNorm2_nonneg (fun i : Fin m => A i j)))
  · exact hdb.trans
      (mul_le_mul_of_nonneg_right hcollapse (vecNorm2_nonneg b))

end

end NumStability
