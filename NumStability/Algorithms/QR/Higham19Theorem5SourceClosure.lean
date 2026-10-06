import NumStability.Algorithms.QR.Higham19Labels
import NumStability.Algorithms.Chapter06Lemma66
import NumStability.Algorithms.LeastSquares.Higham20ZeroDeltaB

/-!
# Higham Theorem 19.5 and equation (19.14): source closure

This file repairs the source-facing gap left by the historical theorem named
`H19_Theorem19_5_qr_solve_columnwise_backward_error`: that theorem returns the
normwise `QRSolveBackwardError` contract, whereas Higham's printed theorem is
columnwise in `A` and uses the vector 2-norm for `b`.

All implementation-facing results below start from the actual zero-aware
`fl_householderQR_solve` executor.  The matrix coefficient keeps the two
operation-derived contributions visible:

* `G = gamma fp (n * householderConstructApplyGammaIndex n)` from the concrete
  Householder QR factorization; and
* `gamma fp n * (1 + G)` from concrete rounded back substitution after
  bounding each computed `R` column by `(1 + G)` times the corresponding input
  column.

For equation (19.14), the source silently uses the inverse of `(Q + dQ)^T`.
Here that nonsingularity step is derived from the proved perturbation bound
`‖dQ‖₂ ≤ B < 1`: after setting `P = (Q + dQ)^T` and `M = P Q`, the matrix
`M = I + dQ^T Q` is inverted by the operator-norm Neumann lemma.  Thus the
source-facing coefficient has no dimension-losing Frobenius bound on an
arbitrary supplied inverse.
-/

namespace NumStability

open scoped BigOperators

set_option maxHeartbeats 1000000

/-! ## Direct Euclidean RHS accumulation

The historical RHS theorem first bounded every perturbation coordinate and
then converted that bound to the 2-norm.  Its recursive coefficient can grow
much faster than Higham's `gamma-tilde_(n^2)` class.  The following contract
instead accumulates the one-reflector residual directly in the Euclidean norm.
-/

/-- Fixed-`Q`, Euclidean relative backward-error contract for the concrete QR
right-hand-side transform. -/
structure Higham19RhsExplicitNormwiseBackwardError (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ) (chat : Fin m → ℝ)
    (c : ℝ) : Prop where
  orth : IsOrthogonal m Q
  result : ∃ db : Fin m → ℝ,
    (∀ i, chat i =
      matMulVec m (matTranspose Q) (fun k => b k + db k) i) ∧
    vecNorm2 db ≤ c * vecNorm2 b

theorem Higham19RhsExplicitNormwiseBackwardError.mono {m p : ℕ}
    {A : Fin m → Fin p → ℝ} {b : Fin m → ℝ}
    {Q : Fin m → Fin m → ℝ} {chat : Fin m → ℝ} {c c' : ℝ}
    (h : Higham19RhsExplicitNormwiseBackwardError m p A b Q chat c)
    (hcc : c ≤ c') :
    Higham19RhsExplicitNormwiseBackwardError m p A b Q chat c' := by
  obtain ⟨db, hrep, hdb⟩ := h.result
  refine ⟨h.orth, db, hrep, le_trans hdb ?_⟩
  exact mul_le_mul_of_nonneg_right hcc (vecNorm2_nonneg b)

/-- Dropping the leading coordinate cannot increase the Euclidean norm. -/
theorem higham19_vecNorm2_vectorTail_le {m : ℕ}
    (x : Fin (m + 1) → ℝ) :
    vecNorm2 (vectorTail x) ≤ vecNorm2 x := by
  rw [vecNorm2, vecNorm2]
  apply Real.sqrt_le_sqrt
  unfold vecNorm2Sq
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg (x 0))

/-- Embedding a tail perturbation with a leading zero preserves its 2-norm. -/
theorem higham19_vecNorm2_vectorTrailingPerturbation {m : ℕ}
    (x : Fin m → ℝ) :
    vecNorm2 (vectorTrailingPerturbation x) = vecNorm2 x := by
  rw [vecNorm2, vecNorm2]
  congr 1
  unfold vecNorm2Sq
  rw [Fin.sum_univ_succ]
  simp [vectorTrailingPerturbation]

theorem higham19_rhs_normwise_zero_rows (p : ℕ)
    (A : Fin 0 → Fin p → ℝ) (b : Fin 0 → ℝ) :
    Higham19RhsExplicitNormwiseBackwardError 0 p A b
      (idMatrix 0) b 0 := by
  let db : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨idMatrix_orthogonal 0, db, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp [db, vecNorm2, vecNorm2Sq]

theorem higham19_rhs_normwise_zero_cols (m : ℕ)
    (A : Fin (m + 1) → Fin 0 → ℝ) (b : Fin (m + 1) → ℝ) :
    Higham19RhsExplicitNormwiseBackwardError (m + 1) 0 A b
      (idMatrix (m + 1)) b 0 := by
  let db : Fin (m + 1) → ℝ := fun _ => 0
  refine ⟨idMatrix_orthogonal (m + 1), db, ?_, ?_⟩
  · intro i
    simp [db, matMulVec, matTranspose, idMatrix, Finset.mem_univ]
  · simp [db, vecNorm2, vecNorm2Sq]

/-- Lift a normwise tail certificate through a skipped zero active column. -/
theorem higham19_rhs_normwise_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ) (ctail : Fin m → ℝ) (alpha : ℝ)
    (_hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail : Higham19RhsExplicitNormwiseBackwardError m p
      (trailingPanel A) (vectorTail b) Qt ctail alpha)
    (halpha : 0 ≤ alpha) :
    Higham19RhsExplicitNormwiseBackwardError (m + 1) (p + 1) A b
      (embedTrailingOne Qt) (vectorFromTopTail (b 0) ctail) alpha := by
  obtain ⟨dtail, hTailRep, hdtail⟩ := hTail.result
  let db : Fin (m + 1) → ℝ := vectorTrailingPerturbation dtail
  refine ⟨embedTrailingOne_orthogonal Qt hTail.orth, db, ?_, ?_⟩
  · have hLift := vectorFromTopTail_lift_trailing_rep Qt
      (b 0) (vectorTail b) ctail dtail hTailRep
    have hInside :
        (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
          vectorTrailingPerturbation dtail i) =
        fun i => b i + db i := by
      ext i
      simp [db]
    intro i
    calc
      vectorFromTopTail (b 0) ctail i =
          matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
            (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
              vectorTrailingPerturbation dtail i) i := congrFun hLift i
      _ = matMulVec (m + 1) (matTranspose (embedTrailingOne Qt))
            (fun i => b i + db i) i := by
          rw [matTranspose_embedTrailingOne, hInside]
  · calc
      vecNorm2 db = vecNorm2 dtail := by
        exact higham19_vecNorm2_vectorTrailingPerturbation dtail
      _ ≤ alpha * vecNorm2 (vectorTail b) := hdtail
      _ ≤ alpha * vecNorm2 b :=
        mul_le_mul_of_nonneg_left (higham19_vecNorm2_vectorTail_le b) halpha

/-- Direct Euclidean cons step.  Its coefficient recurrence is exactly
`alpha + c*(1+alpha)`, the repository's `residualAccumBound` recurrence. -/
theorem higham19_rhs_normwise_cons {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Atail : Fin m → Fin p → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (b y : Fin (m + 1) → ℝ) (ctail : Fin m → ℝ)
    (c alpha : ℝ)
    (hStep : HouseholderAppError (m + 1) P b y c)
    (hTail : Higham19RhsExplicitNormwiseBackwardError m p Atail
      (vectorTail y) Qt ctail alpha)
    (halpha : 0 ≤ alpha) :
    Higham19RhsExplicitNormwiseBackwardError (m + 1) (p + 1) A b
      (matTranspose
        (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P))
      (vectorFromTopTail (y 0) ctail)
      (alpha + c * (1 + alpha)) := by
  obtain ⟨e, hy, dP, hdP, he⟩ := hStep.exists_residual_vector
  obtain ⟨dtail, hTailRep, hdtail⟩ := hTail.result
  let dtailFull : Fin (m + 1) → ℝ := vectorTrailingPerturbation dtail
  let eta : Fin (m + 1) → ℝ := fun i => e i + dtailFull i
  let db : Fin (m + 1) → ℝ := matMulVec (m + 1) (matTranspose P) eta
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := matTranspose M
  have heNorm : vecNorm2 e ≤ c * vecNorm2 b := by
    have hefun : e = matMulVec (m + 1) dP b := by
      funext i
      exact he i
    rw [hefun]
    exact le_trans (vecNorm2_matMulVec_le_frobNorm_mul dP b)
      (mul_le_mul_of_nonneg_right hdP (vecNorm2_nonneg b))
  have hyNorm : vecNorm2 y ≤ (1 + c) * vecNorm2 b := by
    have hyfun : y = fun i => matMulVec (m + 1) P b i + e i := by
      funext i
      exact hy i
    rw [hyfun]
    calc
      vecNorm2 (fun i => matMulVec (m + 1) P b i + e i)
          ≤ vecNorm2 (matMulVec (m + 1) P b) + vecNorm2 e :=
            vecNorm2_add_le _ _
      _ = vecNorm2 b + vecNorm2 e := by
        rw [vecNorm2_orthogonal P b hStep.orth]
      _ ≤ vecNorm2 b + c * vecNorm2 b :=
        add_le_add (le_refl _) heNorm
      _ = (1 + c) * vecNorm2 b := by ring
  have htailY : vecNorm2 (vectorTail y) ≤ (1 + c) * vecNorm2 b :=
    le_trans (higham19_vecNorm2_vectorTail_le y) hyNorm
  have hdtailFull : vecNorm2 dtailFull ≤
      alpha * ((1 + c) * vecNorm2 b) := by
    calc
      vecNorm2 dtailFull = vecNorm2 dtail := by
        exact higham19_vecNorm2_vectorTrailingPerturbation dtail
      _ ≤ alpha * vecNorm2 (vectorTail y) := hdtail
      _ ≤ alpha * ((1 + c) * vecNorm2 b) :=
        mul_le_mul_of_nonneg_left htailY halpha
  refine ⟨?_, db, ?_, ?_⟩
  · have hEmb : IsOrthogonal (m + 1)
        (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hTail.orth.transpose
    have hM : IsOrthogonal (m + 1) M := hEmb.mul hStep.orth
    simpa [Q, M] using hM.transpose
  · have hLift := vectorFromTopTail_lift_trailing_rep Qt
      (y 0) (vectorTail y) ctail dtail hTailRep
    have hPdb : ∀ i, matMulVec (m + 1) P db i = eta i := by
      intro i
      have hPPt : matMul (m + 1) P (matTranspose P) =
          idMatrix (m + 1) := by
        ext a d
        exact hStep.orth.right_inv a d
      calc
        matMulVec (m + 1) P db i =
            matMulVec (m + 1) P
              (matMulVec (m + 1) (matTranspose P) eta) i := rfl
        _ = matMulVec (m + 1)
              (matMul (m + 1) P (matTranspose P)) eta i := by
            exact (matMulVec_matMul (m + 1) P (matTranspose P) eta i).symm
        _ = matMulVec (m + 1) (idMatrix (m + 1)) eta i := by rw [hPPt]
        _ = eta i := congrFun (matMulVec_id (m + 1) eta) i
    have hyEta : (fun i => y i + dtailFull i) =
        matMulVec (m + 1) P (fun k => b k + db k) := by
      ext i
      calc
        y i + dtailFull i =
            (matMulVec (m + 1) P b i + e i) + dtailFull i := by rw [hy i]
        _ = matMulVec (m + 1) P b i + eta i := by simp [eta]; ring
        _ = matMulVec (m + 1) P b i +
            matMulVec (m + 1) P db i := by rw [hPdb i]
        _ = matMulVec (m + 1) P (fun k => b k + db k) i := by
          unfold matMulVec
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    have hLift' : vectorFromTopTail (y 0) ctail =
        matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
          (fun i => y i + dtailFull i) := by
      rw [hLift]
      have hInside :
          (fun i => vectorFromTopTail (y 0) (vectorTail y) i +
            vectorTrailingPerturbation dtail i) =
          fun i => y i + dtailFull i := by
        ext i
        simp [dtailFull]
      rw [hInside]
    intro i
    calc
      vectorFromTopTail (y 0) ctail i =
          matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
            (fun i => y i + dtailFull i) i := congrFun hLift' i
      _ = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
            (matMulVec (m + 1) P (fun k => b k + db k)) i := by rw [hyEta]
      _ = matMulVec (m + 1) M (fun k => b k + db k) i := by
        exact (matMulVec_matMul (m + 1)
          (embedTrailingOne (matTranspose Qt)) P
          (fun k => b k + db k) i).symm
      _ = matMulVec (m + 1) (matTranspose Q)
            (fun k => b k + db k) i := by
        simp [Q, M, matTranspose_involutive]
  · calc
      vecNorm2 db = vecNorm2 eta :=
        vecNorm2_orthogonal (matTranspose P) eta hStep.orth.transpose
      _ ≤ vecNorm2 e + vecNorm2 dtailFull := by
        exact vecNorm2_add_le e dtailFull
      _ ≤ c * vecNorm2 b + alpha * ((1 + c) * vecNorm2 b) :=
        add_le_add heNorm hdtailFull
      _ = (alpha + c * (1 + alpha)) * vecNorm2 b := by ring

/-- Widen the Frobenius perturbation radius in a one-reflector application
certificate. -/
theorem higham19_householderAppError_mono {n : ℕ}
    {P : Fin n → Fin n → ℝ} {b y : Fin n → ℝ} {c c' : ℝ}
    (h : HouseholderAppError n P b y c) (hcc : c ≤ c') :
    HouseholderAppError n P b y c' := by
  obtain ⟨dP, hdP, hrep⟩ := h.pert
  exact ⟨h.orth, dP, le_trans hdP hcc, hrep⟩

/-- Direct Euclidean backward-error theorem for the actual zero-aware panel
RHS recursion, with a uniform ambient-row step coefficient. -/
theorem fl_householderQRPanel_rhs_explicit_normwise_backward_error
    (fp : FPModel) :
    ∀ (m p N : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      m ≤ N → gammaValid fp (11 * N + 23) →
      Higham19RhsExplicitNormwiseBackwardError m p A b
        (fl_householderQRPanel_Q fp m p A)
        (fl_householderQRPanel_rhs fp m p A b)
        (residualAccumBound (householderConstructApplyBound fp N)
          (Nat.min m p)) := by
  intro m
  induction m with
  | zero =>
      intro p N A b _hmN _hvalid
      simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
        residualAccumBound] using higham19_rhs_normwise_zero_rows p A b
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro N A b _hmN _hvalid
          simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
            residualAccumBound] using higham19_rhs_normwise_zero_cols m A b
      | succ p =>
          intro N A b hmN hvalid
          let C := householderConstructApplyBound fp N
          have hC : 0 ≤ C := by
            exact householderConstructApplyBound_nonneg fp N hvalid
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have hTail := ih p N (trailingPanel A) (vectorTail b)
              (by omega) hvalid
            have halpha : 0 ≤ residualAccumBound C (Nat.min m p) :=
              residualAccumBound_nonneg C hC _
            have hskip := higham19_rhs_normwise_skip_zero_column A b
              (fl_householderQRPanel_Q fp m p (trailingPanel A))
              (fl_householderQRPanel_rhs fp m p (trailingPanel A)
                (vectorTail b))
              (residualAccumBound C (Nat.min m p)) hcol
              (by simpa [C] using hTail) halpha
            have hwiden := hskip.mono
              (residualAccumBound_le_succ C hC (Nat.min m p))
            simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
              C, hcol, residualAccumBound] using hwiden
          · have hlocalValid : gammaValid fp (11 * (m + 1) + 23) :=
              gammaValid_mono fp (by omega) hvalid
            let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
              householder (m + 1)
                (householderNormalizedVector (m + 1)
                  (householderVector (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))
                  (householderBetaFromScale (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))) 1
            let bstep : Fin (m + 1) → ℝ :=
              fl_householderApply fp (m + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 b
            have hstepRaw := fl_householder_first_column_rhs_step_error
              fp A b hcol hlocalValid
            have hlocal_le : householderConstructApplyBound fp (m + 1) ≤ C := by
              exact householderConstructApplyBound_mono fp hmN hvalid
            have hstep : HouseholderAppError (m + 1) P b bstep C := by
              apply higham19_householderAppError_mono
                (by simpa [P, bstep] using hstepRaw)
              exact hlocal_le
            have hTail := ih p N
              (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
              (by omega) hvalid
            have halpha : 0 ≤ residualAccumBound C (Nat.min m p) :=
              residualAccumBound_nonneg C hC _
            have hcons := higham19_rhs_normwise_cons A
              (fl_householderTrailingPanelStep fp A) P
              (fl_householderQRPanel_Q fp m p
                (fl_householderTrailingPanelStep fp A))
              b bstep
              (fl_householderQRPanel_rhs fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
              C (residualAccumBound C (Nat.min m p)) hstep
              (by simpa [C] using hTail) halpha
            simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
              fl_householderTrailingPanelStep, C, hcol, P, bstep,
              residualAccumBound] using hcons

/-- Square source-rate specialization of the direct Euclidean recursion.

The local concrete reflector coefficient is first bounded by `gamma K_n`; the
`n`-step `residualAccumBound` is then compressed by
`residualAccumBound_gamma_le_gamma_mul` to `gamma (n*K_n)`.  Since
`K_n = 3*(11*n+23)`, this is an explicit `O(n^2)` gamma index. -/
theorem fl_householderQR_rhs_explicit_normwise_backward_error_gammaHigham
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n)) :
    Higham19RhsExplicitNormwiseBackwardError n n A b
      (fl_householderQR_Q fp n A)
      (fl_householderQR_rhs fp n A b)
      (gamma fp (n * householderConstructApplyGammaIndex n)) := by
  let K := householderConstructApplyGammaIndex n
  let C := householderConstructApplyBound fp n
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * n + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK)
      (by simpa [K] using hvalid)
  have hKvalid : gammaValid fp K :=
    gammaValid_mono fp hK_le_nK (by simpa [K] using hvalid)
  have hraw := fl_householderQRPanel_rhs_explicit_normwise_backward_error
    fp n n n A b le_rfl hbase
  have hC : 0 ≤ C := householderConstructApplyBound_nonneg fp n hbase
  have hCgamma : C ≤ gamma fp K := by
    simpa [C, K] using householderConstructApplyBound_le_gamma fp n hKvalid
  have hmono : residualAccumBound C n ≤
      residualAccumBound (gamma fp K) n :=
    residualAccumBound_mono hC hCgamma n
  have hcompress : residualAccumBound (gamma fp K) n ≤ gamma fp (n * K) :=
    residualAccumBound_gamma_le_gamma_mul fp K n
      (by simpa [K] using hvalid)
  apply hraw.mono
  simpa [C, K] using le_trans hmono hcompress

/-- Dimensionless matrix coefficient obtained by composing the actual
Householder factorization and actual rounded back substitution. -/
noncomputable def higham19Theorem5MatrixCoeff (fp : FPModel) (n : ℕ) : ℝ :=
  let G := gamma fp (n * householderConstructApplyGammaIndex n)
  G + gamma fp n * (1 + G)

/-- Dimensionless RHS coefficient obtained by direct Euclidean accumulation of
the actual rounded Householder applications.  Its explicit index is quadratic
in `n`, matching the source's `gamma-tilde_(n^2)` class. -/
noncomputable def higham19Theorem5RhsCoeff (fp : FPModel) (n : ℕ) : ℝ :=
  gamma fp (n * householderConstructApplyGammaIndex n)

/-- Faithful source-facing contract for Theorem 19.5.  Both constants are
dimensionless relative coefficients, and the matrix perturbation is controlled
column by column. -/
structure Higham19Theorem5ColumnwiseBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (cA cb : ℝ) : Prop where
  result : ∃ (dA : Fin n → Fin n → ℝ) (db : Fin n → ℝ),
    (∀ i, matMulVec n (fun r j => A r j + dA r j) xhat i = b i + db i) ∧
    (∀ j, columnFrob dA j ≤ cA * columnFrob A j) ∧
    vecNorm2 db ≤ cb * vecNorm2 b

/-- Source-facing contract for the unperturbed-right-hand-side form (19.14). -/
structure Higham19Eq1914ColumnwiseBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (cA : ℝ) : Prop where
  result : ∃ dA : Fin n → Fin n → ℝ,
    (∀ i, matMulVec n (fun r j => A r j + dA r j) xhat i = b i) ∧
    (∀ j, columnFrob dA j ≤ cA * columnFrob A j)

/-- Entrywise relative domination implies the corresponding column-2-norm
domination.  This local lemma avoids importing a later chapter merely for a
one-column norm conversion. -/
theorem higham19_columnFrob_le_of_entrywise_relative_bound {m n : ℕ}
    (A dA : Fin m → Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hentry : ∀ i j, |dA i j| ≤ c * |A i j|) (j : Fin n) :
    columnFrob dA j ≤ c * columnFrob A j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  calc
    vecNorm2 (fun i : Fin m => dA i j)
        ≤ vecNorm2 (fun i : Fin m => c * |A i j|) := by
          apply vecNorm2_le_of_abs_le
          intro i
          simpa [abs_mul, abs_of_nonneg hc] using hentry i j
    _ = c * vecNorm2 (fun i : Fin m => A i j) := by
          rw [vecNorm2_smul, abs_of_nonneg hc, vecNorm2_abs]

/-- A square matrix acting on a rectangular matrix controls every output
column by its Frobenius norm. -/
theorem higham19_columnFrob_matMul_le {n p : ℕ}
    (M : Fin n → Fin n → ℝ) (A : Fin n → Fin p → ℝ) (j : Fin p) :
    columnFrob (matMulRect n n p M A) j ≤ frobNorm M * columnFrob A j := by
  exact columnFrob_matMulVec_le_frobNorm_mul_columnFrob
    (matMulRect n n p M A) A M j (by
      intro i
      rfl)

/-- An operator-2 certificate for a square left factor controls every output
column without the dimension loss of replacing it by a Frobenius norm. -/
theorem higham19_columnFrob_matMul_le_of_opNorm2Le {n p : ℕ}
    (M : Fin n → Fin n → ℝ) (A : Fin n → Fin p → ℝ) {c : ℝ}
    (hM : opNorm2Le M c) (j : Fin p) :
    columnFrob (matMulRect n n p M A) j ≤ c * columnFrob A j := by
  exact columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob M A
    (opNorm2Le_to_rectOpNorm2Le hM) j

/-- Columnwise triangle inequality for subtraction. -/
theorem higham19_columnFrob_sub_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (j : Fin n) :
    columnFrob (fun i k => A i k - B i k) j ≤
      columnFrob A j + columnFrob B j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2,
    columnFrob_eq_vecNorm2]
  have h := vecNorm2_add_le (fun i : Fin m => A i j)
    (fun i : Fin m => -B i j)
  simpa [sub_eq_add_neg, vecNorm2_neg] using h

/-- The columnwise composition theorem behind Theorem 19.5.  It combines a
fixed-`Q` columnwise QR certificate, an actual back-substitution perturbation,
and the actual fixed-`Q` RHS transform. -/
theorem higham19_theorem5_columnwise_from_components
    (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (b xhat chat : Fin n → ℝ)
    (Q R dA1 dR : Fin n → Fin n → ℝ)
    (db : Fin n → ℝ) (etaQR etaR etaB : ℝ)
    (hQ : IsOrthogonal n Q)
    (hR : ∀ i j, R i j =
      matMul n (matTranspose Q) (fun r k => A r k + dA1 r k) i j)
    (hAcol : ∀ j, columnFrob dA1 j ≤ etaQR * columnFrob A j)
    (hSolve : ∀ i, matMulVec n (fun r j => R r j + dR r j) xhat i = chat i)
    (hRentry : ∀ i j, |dR i j| ≤ etaR * |R i j|)
    (hchat : ∀ i, chat i =
      matMulVec n (matTranspose Q) (fun k => b k + db k) i)
    (hdb : vecNorm2 db ≤ etaB * vecNorm2 b)
    (hetaR : 0 ≤ etaR) :
    Higham19Theorem5ColumnwiseBackwardError n A b xhat
      (etaQR + etaR * (1 + etaQR)) etaB := by
  let dA : Fin n → Fin n → ℝ :=
    fun i j => dA1 i j + matMul n Q dR i j
  have hQR : ∀ i j, matMul n Q R i j = A i j + dA1 i j := by
    intro i j
    have hRmat : R =
        matMul n (matTranspose Q) (fun r k => A r k + dA1 r k) := by
      ext r k
      exact hR r k
    rw [hRmat, ← matMul_assoc]
    have hQQt : matMul n Q (matTranspose Q) = idMatrix n := by
      ext r k
      exact hQ.right_inv r k
    rw [hQQt, matMul_id_left]
  have hRcol : ∀ j, columnFrob R j ≤ (1 + etaQR) * columnFrob A j := by
    intro j
    have horthcol :
        columnFrob R j = columnFrob (fun r k => A r k + dA1 r k) j := by
      have hRmat : R =
          matMul n (matTranspose Q) (fun r k => A r k + dA1 r k) := by
        ext r k
        exact hR r k
      rw [hRmat]
      exact columnFrob_orthogonal_left
        (matTranspose Q) (fun r k => A r k + dA1 r k) hQ.transpose j
    rw [horthcol]
    calc
      columnFrob (fun r k => A r k + dA1 r k) j
          ≤ columnFrob A j + columnFrob dA1 j :=
            columnFrob_add_le A dA1 j
      _ ≤ columnFrob A j + etaQR * columnFrob A j :=
            add_le_add (le_refl (columnFrob A j)) (hAcol j)
      _ = (1 + etaQR) * columnFrob A j := by ring
  have hdRcol : ∀ j, columnFrob dR j ≤
      etaR * ((1 + etaQR) * columnFrob A j) := by
    intro j
    exact le_trans
      (higham19_columnFrob_le_of_entrywise_relative_bound R dR hetaR hRentry j)
      (mul_le_mul_of_nonneg_left (hRcol j) hetaR)
  have hdAcol : ∀ j, columnFrob dA j ≤
      (etaQR + etaR * (1 + etaQR)) * columnFrob A j := by
    intro j
    have hQdR : columnFrob (matMul n Q dR) j = columnFrob dR j :=
      columnFrob_orthogonal_left Q dR hQ j
    calc
      columnFrob dA j
          ≤ columnFrob dA1 j + columnFrob (matMul n Q dR) j := by
            exact columnFrob_add_le dA1 (matMul n Q dR) j
      _ = columnFrob dA1 j + columnFrob dR j := by rw [hQdR]
      _ ≤ etaQR * columnFrob A j +
          etaR * ((1 + etaQR) * columnFrob A j) :=
            add_le_add (hAcol j) (hdRcol j)
      _ = (etaQR + etaR * (1 + etaQR)) * columnFrob A j := by ring
  refine ⟨dA, db, ?_, hdAcol, hdb⟩
  intro i
  have hmat :
      (fun r j => A r j + dA r j) =
        fun r j => A r j + dA1 r j + matMul n Q dR r j := by
    ext r j
    simp [dA]
    ring
  rw [hmat]
  exact qr_solve_backward_from_components n hn A Q R dA1 hQ hQR
    (le_refl (frobNorm dA1)) xhat chat dR hSolve
    (le_refl (frobNorm dR)) b db hchat i

/-- **Higham Theorem 19.5, actual-executor columnwise closure.**

The witnesses are derived from `fl_householderQR_solve`, the actual fixed-`Q`
columnwise Householder QR theorem, the actual RHS transformation, and
`backSub_backward_error`.  No backward-error target is assumed. -/
theorem higham19_theorem19_5_actual_columnwise_backward_error
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    Higham19Theorem5ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Theorem5MatrixCoeff fp n)
      (higham19Theorem5RhsCoeff fp n) := by
  let K := householderConstructApplyGammaIndex n
  let G := gamma fp (n * K)
  let gn := gamma fp n
  let Q := fl_householderQR_Q fp n A
  let R := fl_householderQR_R fp n A
  let chat := fl_householderQR_rhs fp n A b
  have hQR :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp n n A (by simpa using hn) (by simpa [K] using hvalid)
  obtain ⟨dA1, hR, _hAnorm, hAcol⟩ := hQR.result
  have hQ : IsOrthogonal n Q := by simpa [Q] using hQR.orth
  have hRhs :=
    fl_householderQR_rhs_explicit_normwise_backward_error_gammaHigham
      fp n A b hn hvalid
  obtain ⟨db, hchat, hdb⟩ := hRhs.result
  have hnvalid : gammaValid fp n :=
    gammaValid_mono fp (by
      have hKpos : 0 < K := by
        dsimp [K, householderConstructApplyGammaIndex]
        omega
      exact Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hUT : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R, IsUpperTriangular] using fl_householderQR_R_upper fp n A
  obtain ⟨dR, hRentry, hSolve⟩ :=
    backSub_backward_error fp n R chat
      (by simpa [R] using hdiag) hUT hnvalid
  have hcol := higham19_theorem5_columnwise_from_components
    n hn A b (fl_householderQR_solve fp n A b) chat Q R dA1 dR db
    G gn (higham19Theorem5RhsCoeff fp n) hQ
    (by simpa [R, Q] using hR) (by simpa [G] using hAcol)
    (by
      intro i
      simpa [R, chat, fl_householderQR_solve] using hSolve i)
    (by simpa [gn] using hRentry)
    (by simpa [chat, Q] using hchat) hdb
    (by simpa [gn] using gamma_nonneg fp hnvalid)
  simpa [higham19Theorem5MatrixCoeff, G, gn, K] using hcol

/-! ## Equation (19.14): absorbing the RHS perturbation -/

/-- Modular coefficient obtained when a caller supplies a Frobenius bound
`tau` on a left inverse of `(Q + dQ)^T`.  This remains useful as an algebraic
adapter, but is not the source-closing coefficient: even an orthogonal inverse
has Frobenius norm `sqrt n`, so `tau` would lose a dimension factor. -/
noncomputable def higham19Eq1914AbsorbCoeff
    (fp : FPModel) (n : ℕ) (tau : ℝ) : ℝ :=
  let G := gamma fp (n * householderConstructApplyGammaIndex n)
  let B := higham19Theorem5RhsCoeff fp n
  G + tau * (B + gamma fp n) * (1 + G)

/-- Dimension-faithful coefficient for equation (19.14).  The inverse action
is bounded in operator 2-norm by `(1-B)⁻¹`, where
`B = higham19Theorem5RhsCoeff fp n`; hence no `sqrt n` factor is introduced. -/
noncomputable def higham19Eq1914SourceCoeff
    (fp : FPModel) (n : ℕ) : ℝ :=
  let G := gamma fp (n * householderConstructApplyGammaIndex n)
  let B := higham19Theorem5RhsCoeff fp n
  G + (1 / (1 - B)) * (B + gamma fp n) * (1 + G)

/-- Explicit certification of the `gamma-tilde_(n^2)` classification printed
in (19.14).  The Householder construction/application index is quadratic in
`n`; under the standard quarter-radius guard the exact rational coefficient
is at most fourteen times that index times unit roundoff. -/
theorem higham19Eq1914SourceCoeff_le_fourteen_index_mul_unit_roundoff_of_small
    (fp : FPModel) (n : ℕ)
    (hsmall :
      (((n * householderConstructApplyGammaIndex n : ℕ) : ℝ) * fp.u ≤
        1 / 4)) :
    higham19Eq1914SourceCoeff fp n ≤
      14 * ((n * householderConstructApplyGammaIndex n : ℕ) : ℝ) * fp.u := by
  let K := householderConstructApplyGammaIndex n
  let N := n * K
  let G := gamma fp N
  let gn := gamma fp n
  have hNsmall : (N : ℝ) * fp.u ≤ 1 / 4 := by simpa [N, K] using hsmall
  have hNhalf : (N : ℝ) * fp.u ≤ 1 / 2 := by linarith
  have hNvalid : gammaValid fp N := by
    unfold gammaValid
    linarith
  have hG0 : 0 ≤ G := by simpa [G] using gamma_nonneg fp hNvalid
  have hGlin : G ≤ 2 * ((N : ℝ) * fp.u) := by
    simpa [G] using gamma_le_two_mul_n_u_of_nu_le_half fp N hNhalf
  have hGhalf : G ≤ 1 / 2 := by linarith
  have hKpos : 0 < K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hnN : n ≤ N := by
    exact Nat.le_mul_of_pos_right n hKpos
  have hgn0 : 0 ≤ gn := by
    have hnvalid := gammaValid_mono fp hnN hNvalid
    simpa [gn] using gamma_nonneg fp hnvalid
  have hgnG : gn ≤ G := by
    simpa [gn, G] using gamma_mono fp hnN hNvalid
  have htau2 : 1 / (1 - G) ≤ 2 := by
    calc
      1 / (1 - G) ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hprod0 : 0 ≤ (G + gn) * (1 + G) :=
    mul_nonneg (add_nonneg hG0 hgn0) (by linarith)
  calc
    higham19Eq1914SourceCoeff fp n
        = G + (1 / (1 - G)) * (G + gn) * (1 + G) := by
          simp [higham19Eq1914SourceCoeff, G, gn, N, K,
            higham19Theorem5RhsCoeff]
    _ ≤ G + 2 * (G + gn) * (1 + G) := by
          have hscaled := mul_le_mul_of_nonneg_right htau2 hprod0
          convert add_le_add_left hscaled G using 1 <;> ring
    _ ≤ G + 2 * (G + G) * (1 + G) := by
          gcongr
    _ ≤ G + 2 * (G + G) * (1 + 1 / 2) := by
          gcongr
    _ = 7 * G := by ring
    _ ≤ 14 * (N : ℝ) * fp.u := by
          nlinarith [hGlin]
    _ = 14 * ((n * householderConstructApplyGammaIndex n : ℕ) : ℝ) * fp.u := by
          simp [N, K]

/-- Exact algebraic (19.14) absorption theorem.

The hypothesis `hleft` says that `T` is a left inverse of `(Q + dQ)^T`; `hT`
is its operator-2 action bound.  This component theorem does not assume any
form of the desired perturbed system. -/
theorem higham19_eq19_14_columnwise_from_components
    (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b xhat chat : Fin n → ℝ)
    (Q R dA1 dR dQ T : Fin n → Fin n → ℝ)
    (etaQR etaR etaQ tau : ℝ)
    (hQ : IsOrthogonal n Q)
    (hR : ∀ i j, R i j =
      matMul n (matTranspose Q) (fun r k => A r k + dA1 r k) i j)
    (hAcol : ∀ j, columnFrob dA1 j ≤ etaQR * columnFrob A j)
    (hSolve : ∀ i, matMulVec n (fun r j => R r j + dR r j) xhat i = chat i)
    (hRentry : ∀ i j, |dR i j| ≤ etaR * |R i j|)
    (hchat : ∀ i, chat i =
      matMulVec n (fun r k => Q k r + dQ k r) b i)
    (hdQ : frobNorm dQ ≤ etaQ)
    (hleft : ∀ i j,
      matMul n T (fun r k => Q k r + dQ k r) i j = idMatrix n i j)
    (hT : opNorm2Le T tau)
    (hetaR : 0 ≤ etaR) (hetaQ : 0 ≤ etaQ) (htau : 0 ≤ tau) :
    Higham19Eq1914ColumnwiseBackwardError n A b xhat
      (etaQR + tau * (etaQ + etaR) * (1 + etaQR)) := by
  let Ap : Fin n → Fin n → ℝ := fun i j => A i j + dA1 i j
  let dQt : Fin n → Fin n → ℝ := matTranspose dQ
  let dA : Fin n → Fin n → ℝ := fun i j =>
    dA1 i j + matMul n T dR i j -
      matMul n T (matMul n dQt Ap) i j
  have hRmat : R = matMul n (matTranspose Q) Ap := by
    ext i j
    simpa [Ap] using hR i j
  have hleftmat :
      matMul n T (fun r k => Q k r + dQ k r) = idMatrix n := by
    ext i j
    exact hleft i j
  have hTQ : matMul n T (matTranspose Q) =
      fun i j => idMatrix n i j - matMul n T dQt i j := by
    have hadd : (fun r k => Q k r + dQ k r) =
        fun r k => matTranspose Q r k + dQt r k := by
      rfl
    rw [hadd, matMul_add_right] at hleftmat
    ext i j
    have hij := congrFun (congrFun hleftmat i) j
    linarith
  have hTR : matMul n T R =
      fun i j => Ap i j - matMul n T (matMul n dQt Ap) i j := by
    rw [hRmat, ← matMul_assoc, hTQ]
    rw [← matMul_assoc n T dQt Ap]
    ext i j
    unfold matMul
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp [idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
  have hfactor : matMul n T (fun i j => R i j + dR i j) =
      fun i j => A i j + dA i j := by
    rw [matMul_add_right, hTR]
    ext i j
    simp only [dA, Ap]
    ring
  have heq : ∀ i,
      matMulVec n (fun r j => A r j + dA r j) xhat i = b i := by
    have hSolveVec :
        matMulVec n (fun r j => R r j + dR r j) xhat = chat := by
      funext i
      exact hSolve i
    have hchatVec : chat =
        matMulVec n (fun r k => Q k r + dQ k r) b := by
      funext i
      exact hchat i
    intro i
    calc
      matMulVec n (fun r j => A r j + dA r j) xhat i
          = matMulVec n (matMul n T (fun r j => R r j + dR r j)) xhat i := by
              rw [hfactor]
      _ = matMulVec n T
          (matMulVec n (fun r j => R r j + dR r j) xhat) i :=
            matMulVec_matMul n T (fun r j => R r j + dR r j) xhat i
      _ = matMulVec n T chat i := by
            rw [hSolveVec]
      _ = matMulVec n T
          (matMulVec n (fun r k => Q k r + dQ k r) b) i := by
            rw [hchatVec]
      _ = matMulVec n
          (matMul n T (fun r k => Q k r + dQ k r)) b i := by
            exact (matMulVec_matMul n T
              (fun r k => Q k r + dQ k r) b i).symm
      _ = matMulVec n (idMatrix n) b i := by rw [hleftmat]
      _ = b i := congrFun (matMulVec_id n b) i
  have hRcol : ∀ j, columnFrob R j ≤ (1 + etaQR) * columnFrob A j := by
    intro j
    have horthcol : columnFrob R j = columnFrob Ap j := by
      rw [hRmat]
      exact columnFrob_orthogonal_left (matTranspose Q) Ap hQ.transpose j
    rw [horthcol]
    calc
      columnFrob Ap j ≤ columnFrob A j + columnFrob dA1 j := by
        simpa [Ap] using columnFrob_add_le A dA1 j
      _ ≤ columnFrob A j + etaQR * columnFrob A j :=
        add_le_add (le_refl _) (hAcol j)
      _ = (1 + etaQR) * columnFrob A j := by ring
  have hdRcol : ∀ j, columnFrob dR j ≤
      etaR * ((1 + etaQR) * columnFrob A j) := by
    intro j
    exact le_trans
      (higham19_columnFrob_le_of_entrywise_relative_bound R dR hetaR hRentry j)
      (mul_le_mul_of_nonneg_left (hRcol j) hetaR)
  have hApcol : ∀ j, columnFrob Ap j ≤
      (1 + etaQR) * columnFrob A j := by
    intro j
    calc
      columnFrob Ap j ≤ columnFrob A j + columnFrob dA1 j := by
        simpa [Ap] using columnFrob_add_le A dA1 j
      _ ≤ columnFrob A j + etaQR * columnFrob A j :=
        add_le_add (le_refl _) (hAcol j)
      _ = (1 + etaQR) * columnFrob A j := by ring
  have hdQt : frobNorm dQt ≤ etaQ := by
    simpa [dQt, frobNorm_transpose] using hdQ
  have hdQtAp : ∀ j, columnFrob (matMul n dQt Ap) j ≤
      etaQ * ((1 + etaQR) * columnFrob A j) := by
    intro j
    calc
      columnFrob (matMul n dQt Ap) j
          ≤ frobNorm dQt * columnFrob Ap j :=
            higham19_columnFrob_matMul_le dQt Ap j
      _ ≤ etaQ * ((1 + etaQR) * columnFrob A j) :=
            mul_le_mul hdQt (hApcol j) (columnFrob_nonneg Ap j) hetaQ
  have hTdR : ∀ j, columnFrob (matMul n T dR) j ≤
      tau * (etaR * ((1 + etaQR) * columnFrob A j)) := by
    intro j
    calc
      columnFrob (matMul n T dR) j
          ≤ tau * columnFrob dR j :=
            higham19_columnFrob_matMul_le_of_opNorm2Le T dR hT j
      _ ≤ tau * (etaR * ((1 + etaQR) * columnFrob A j)) :=
            mul_le_mul_of_nonneg_left (hdRcol j) htau
  have hTdQtAp : ∀ j,
      columnFrob (matMul n T (matMul n dQt Ap)) j ≤
        tau * (etaQ * ((1 + etaQR) * columnFrob A j)) := by
    intro j
    calc
      columnFrob (matMul n T (matMul n dQt Ap)) j
          ≤ tau * columnFrob (matMul n dQt Ap) j :=
            higham19_columnFrob_matMul_le_of_opNorm2Le T
              (matMul n dQt Ap) hT j
      _ ≤ tau * (etaQ * ((1 + etaQR) * columnFrob A j)) :=
            mul_le_mul_of_nonneg_left (hdQtAp j) htau
  refine ⟨dA, heq, ?_⟩
  intro j
  calc
    columnFrob dA j
        ≤ columnFrob (fun i k => dA1 i k + matMul n T dR i k) j +
            columnFrob (matMul n T (matMul n dQt Ap)) j := by
          simpa [dA] using higham19_columnFrob_sub_le
            (fun i k => dA1 i k + matMul n T dR i k)
            (matMul n T (matMul n dQt Ap)) j
    _ ≤ (columnFrob dA1 j + columnFrob (matMul n T dR) j) +
          columnFrob (matMul n T (matMul n dQt Ap)) j := by
          exact add_le_add (columnFrob_add_le dA1 (matMul n T dR) j) le_rfl
    _ ≤ (etaQR * columnFrob A j +
          tau * (etaR * ((1 + etaQR) * columnFrob A j))) +
          tau * (etaQ * ((1 + etaQR) * columnFrob A j)) :=
        add_le_add (add_le_add (hAcol j) (hTdR j)) (hTdQtAp j)
    _ = (etaQR + tau * (etaQ + etaR) * (1 + etaQR)) *
          columnFrob A j := by ring

/-- Modular actual-executor adapter with a caller-supplied *Frobenius*-bounded
inverse.  It is intentionally not advertised as equation (19.14) closure,
because such a bound incurs a `sqrt n` loss even when the inverse is
orthogonal.  The source-closing operator-norm theorem follows below. -/
theorem higham19_eq19_14_actual_columnwise_nonzero_rhs_of_uniform_frob_inverse_bound
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b ≠ 0) (tau : ℝ) (htau : 0 ≤ tau)
    (hinverse : ∀ dQ : Fin n → Fin n → ℝ,
      frobNorm dQ ≤ higham19Theorem5RhsCoeff fp n →
      ∃ T : Fin n → Fin n → ℝ,
        (∀ i j, matMul n T
          (fun r k => fl_householderQR_Q fp n A k r + dQ k r) i j =
            idMatrix n i j) ∧
        frobNorm T ≤ tau) :
    Higham19Eq1914ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Eq1914AbsorbCoeff fp n tau) := by
  let K := householderConstructApplyGammaIndex n
  let G := gamma fp (n * K)
  let gn := gamma fp n
  let B := higham19Theorem5RhsCoeff fp n
  let Q := fl_householderQR_Q fp n A
  let R := fl_householderQR_R fp n A
  let chat := fl_householderQR_rhs fp n A b
  have hQR :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp n n A (by simpa using hn) (by simpa [K] using hvalid)
  obtain ⟨dA1, hR, _hAnorm, hAcol⟩ := hQR.result
  have hQ : IsOrthogonal n Q := by simpa [Q] using hQR.orth
  have hnvalid : gammaValid fp n := by
    have hKpos : 0 < K := by
      dsimp [K, householderConstructApplyGammaIndex]
      omega
    exact gammaValid_mono fp (Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hRhs :=
    fl_householderQR_rhs_explicit_normwise_backward_error_gammaHigham
      fp n A b hn hvalid
  obtain ⟨db, hchat, hdbGamma⟩ := hRhs.result
  have hdb : vecNorm2 db ≤ B * vecNorm2 b := by
    simpa [B, higham19Theorem5RhsCoeff] using hdbGamma
  obtain ⟨dQ, hQb, hdQ⟩ :=
    H19_Lemma19_3_vector_QplusDeltaQ_form Q hQ b chat db hb
      (by simpa [Q, chat] using hchat) hdb
  obtain ⟨T, hleft, hT⟩ := hinverse dQ (by simpa [B] using hdQ)
  have hUT : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R, IsUpperTriangular] using fl_householderQR_R_upper fp n A
  obtain ⟨dR, hRentry, hSolve⟩ :=
    backSub_backward_error fp n R chat
      (by simpa [R] using hdiag) hUT hnvalid
  have hout := higham19_eq19_14_columnwise_from_components
    n A b (fl_householderQR_solve fp n A b) chat Q R dA1 dR dQ T
    G gn B tau hQ
    (by simpa [R, Q] using hR) (by simpa [G] using hAcol)
    (by
      intro i
      simpa [R, chat, fl_householderQR_solve] using hSolve i)
    (by simpa [gn] using hRentry)
    (by simpa [Q, chat] using hQb)
    (by simpa [B] using hdQ)
    (by simpa [Q] using hleft) (opNorm2Le_of_frobNorm_le T hT)
    (by simpa [gn] using gamma_nonneg fp hnvalid)
    (by
      simpa [B, higham19Theorem5RhsCoeff, K] using gamma_nonneg fp hvalid)
    htau
  simpa [higham19Eq1914AbsorbCoeff, G, gn, B, K] using hout

/-- **Equation (19.14), actual executor, nonzero RHS.**

The source's omitted inverse is constructed rather than assumed.  For the
perturbation `dQ` delivered by Lemma 19.3, put
`P = (Q+dQ)^T`, `M = P Q = I+dQ^T Q`, and
`T = Q M⁻¹`.  The hypothesis `B < 1` and `‖dQ‖₂ ≤ ‖dQ‖F ≤ B` make `M`
nonsingular and give `‖T‖₂ ≤ (1-B)⁻¹`.  Consequently the displayed
coefficient is of the source's quadratic-index gamma-tilde class, with no
spurious `sqrt n` from a Frobenius norm of `T`. -/
theorem higham19_eq19_14_actual_columnwise_nonzero_rhs
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b ≠ 0)
    (hsmall : higham19Theorem5RhsCoeff fp n < 1) :
    Higham19Eq1914ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Eq1914SourceCoeff fp n) := by
  let K := householderConstructApplyGammaIndex n
  let G := gamma fp (n * K)
  let gn := gamma fp n
  let B := higham19Theorem5RhsCoeff fp n
  let Q := fl_householderQR_Q fp n A
  let R := fl_householderQR_R fp n A
  let chat := fl_householderQR_rhs fp n A b
  have hQR :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp n n A (by simpa using hn) (by simpa [K] using hvalid)
  obtain ⟨dA1, hR, _hAnorm, hAcol⟩ := hQR.result
  have hQ : IsOrthogonal n Q := by simpa [Q] using hQR.orth
  have hnvalid : gammaValid fp n := by
    have hKpos : 0 < K := by
      dsimp [K, householderConstructApplyGammaIndex]
      omega
    exact gammaValid_mono fp (Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hB0 : 0 ≤ B := by
    simpa [B, higham19Theorem5RhsCoeff, K] using gamma_nonneg fp hvalid
  have hBlt : B < 1 := by simpa [B] using hsmall
  have hRhs :=
    fl_householderQR_rhs_explicit_normwise_backward_error_gammaHigham
      fp n A b hn hvalid
  obtain ⟨db, hchat, hdbGamma⟩ := hRhs.result
  have hdb : vecNorm2 db ≤ B * vecNorm2 b := by
    simpa [B, higham19Theorem5RhsCoeff] using hdbGamma
  obtain ⟨dQ, hQb, hdQ⟩ :=
    H19_Lemma19_3_vector_QplusDeltaQ_form Q hQ b chat db hb
      (by simpa [Q, chat] using hchat) hdb
  let P : Fin n → Fin n → ℝ := fun i j => Q j i + dQ j i
  let dQt : Fin n → Fin n → ℝ := matTranspose dQ
  let M : Fin n → Fin n → ℝ := matMul n P Q
  let Minv : Fin n → Fin n → ℝ :=
    Theorem20_3_ZeroDeltaB.squareInverse M
  let tau : ℝ := 1 / (1 - B)
  let T : Fin n → Fin n → ℝ := matMul n Q Minv
  have hQtQ : matMul n (matTranspose Q) Q = idMatrix n := by
    ext i j
    exact hQ.left_inv i j
  have hMrep : M = fun i j =>
      idMatrix n i j + matMul n dQt Q i j := by
    dsimp [M, P, dQt]
    change matMul n
      (fun i j => matTranspose Q i j + matTranspose dQ i j) Q = _
    rw [matMul_add_left, hQtQ]
  have hMdef : opNorm2Le (fun i j => M i j - idMatrix n i j) B := by
    have hdQop : opNorm2Le dQ B :=
      opNorm2Le_of_frobNorm_le dQ (by simpa [B] using hdQ)
    have hdQtop : opNorm2Le dQt B := by
      exact opNorm2Le_transpose dQ hB0 (by simpa [dQt] using hdQop)
    have hprod : opNorm2Le (matMul n dQt Q) (B * 1) :=
      opNorm2Le_matMul_square_of_bounds dQt Q hB0 hdQtop hQ.opNorm2Le_one
    have heq : (fun i j => M i j - idMatrix n i j) = matMul n dQt Q := by
      ext i j
      rw [hMrep]
      ring
    simpa [heq] using hprod
  obtain ⟨hMunit, hMinv⟩ :=
    Theorem20_3_ZeroDeltaB.identity_perturbation_unit_and_inverse_action
      M hMdef hBlt
  have htau0 : 0 ≤ tau := by
    dsimp [tau]
    exact (one_div_pos.mpr (sub_pos.mpr hBlt)).le
  have hTop : opNorm2Le T tau := by
    have hprod := opNorm2Le_matMul_square_of_bounds Q Minv
      (by norm_num : (0 : ℝ) ≤ 1) hQ.opNorm2Le_one
      (by simpa [Minv, tau] using hMinv)
    simpa [T, tau, one_div] using hprod
  have hMMi : matMul n M Minv = idMatrix n := by
    have hmat :=
      Matrix.mul_nonsing_inv (M : Matrix (Fin n) (Fin n) ℝ) hMunit
    ext i j
    have hij := congrFun (congrFun hmat i) j
    simpa [Minv, Theorem20_3_ZeroDeltaB.squareInverse,
      matMul, idMatrix, Matrix.mul_apply] using hij
  have hPT : matMul n P T = idMatrix n := by
    dsimp [T]
    rw [← matMul_assoc, show matMul n P Q = M by rfl, hMMi]
  have hright : IsRightInverse n P T := by
    intro i j
    have hij := congrFun (congrFun hPT i) j
    simpa [matMul, idMatrix] using hij
  have hleftPred : IsLeftInverse n P T :=
    isLeftInverse_of_isRightInverse P T hright
  have hleft : ∀ i j, matMul n T P i j = idMatrix n i j := by
    intro i j
    simpa [matMul, idMatrix] using hleftPred i j
  have hUT : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R, IsUpperTriangular] using fl_householderQR_R_upper fp n A
  obtain ⟨dR, hRentry, hSolve⟩ :=
    backSub_backward_error fp n R chat
      (by simpa [R] using hdiag) hUT hnvalid
  have hout := higham19_eq19_14_columnwise_from_components
    n A b (fl_householderQR_solve fp n A b) chat Q R dA1 dR dQ T
    G gn B tau hQ
    (by simpa [R, Q] using hR) (by simpa [G] using hAcol)
    (by
      intro i
      simpa [R, chat, fl_householderQR_solve] using hSolve i)
    (by simpa [gn] using hRentry)
    (by simpa [Q, chat, P] using hQb)
    (by simpa [B] using hdQ)
    (by simpa [Q, P] using hleft) hTop
    (by simpa [gn] using gamma_nonneg fp hnvalid)
    hB0 htau0
  simpa [higham19Eq1914SourceCoeff, G, gn, B, tau, K] using hout

/-- **Equation (19.14), actual executor, zero RHS.**  When `b = 0`, the
implementation-derived Theorem 19.5 RHS perturbation has 2-norm zero, so it is
identically zero and no `(Q + dQ)^T` inverse is needed. -/
theorem higham19_eq19_14_actual_columnwise_zero_rhs
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b = 0) :
    Higham19Eq1914ColumnwiseBackwardError n A b
      (fl_householderQR_solve fp n A b)
      (higham19Theorem5MatrixCoeff fp n) := by
  have hmain := higham19_theorem19_5_actual_columnwise_backward_error
    fp n A b hn hvalid hdiag
  obtain ⟨dA, db, heq, hcol, hdb⟩ := hmain.result
  have hb_norm : vecNorm2 b = 0 := by
    subst b
    rw [vecNorm2]
    simp [vecNorm2Sq]
  have hdb_le : vecNorm2 db ≤ 0 := by
    calc
      vecNorm2 db ≤ higham19Theorem5RhsCoeff fp n * vecNorm2 b := hdb
      _ = 0 := by rw [hb_norm]; ring
  have hdb_norm : vecNorm2 db = 0 :=
    le_antisymm hdb_le (vecNorm2_nonneg db)
  have hdb_zero : ∀ i, db i = 0 := (vecNorm2_eq_zero_iff db).mp hdb_norm
  refine ⟨dA, ?_, hcol⟩
  intro i
  simpa [hdb_zero i] using heq i

/-! ## §19.7: the explicit Lemma 6.6 residual bridge -/

/-- The Chapter 6 complex column norm specializes exactly to the real
`columnFrob` used by the QR development. -/
theorem higham19_lemma66_colNorm2_real_eq_columnFrob {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    Lemma66.lemma66_colNorm2 (fun i k => (A i k : ℂ)) j =
      columnFrob A j := by
  rw [columnFrob_eq_vecNorm2]
  unfold Lemma66.lemma66_colNorm2 Lemma66.lemma66_colNormSq
    vecNorm2 vecNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- **Higham §19.7, precise Lemma 6.6 bridge.**

From the unperturbed-RHS columnwise certificate (19.14), derive the exact
componentwise residual inequality

`|b - A*xhat| <= cA * e*e^T*|A|*|xhat|`.

The right side is written pointwise as the corresponding finite sum.  The
critical entry bound is obtained by applying the already formalized complex
`Lemma66.lemma66_a_abs_entry_le` to the real matrices embedded in `ℂ`.
The subsequent qualitative Theorem 12.4 sentence in the source uses undefined
`≈` and “small”; this theorem intentionally stops at the last precise formula.
-/
theorem higham19_section19_7_lemma66_residual_bridge
    {n : ℕ} {A : Fin n → Fin n → ℝ} {b xhat : Fin n → ℝ}
    {cA : ℝ}
    (h : Higham19Eq1914ColumnwiseBackwardError n A b xhat cA)
    (hcA : 0 ≤ cA) :
    ∀ i,
      |b i - matMulVec n A xhat i| ≤
        cA * ∑ j : Fin n, (∑ k : Fin n, |A k j|) * |xhat j| := by
  obtain ⟨dA, heq, hcol⟩ := h.result
  let dAc : CMatrix n n := fun i j => (dA i j : ℂ)
  let cAc : CMatrix n n := fun i j => ((cA * A i j : ℝ) : ℂ)
  have hcAc_col : ∀ j,
      Lemma66.lemma66_colNorm2 dAc j ≤
        Lemma66.lemma66_colNorm2 cAc j := by
    intro j
    have hdAc_eq : Lemma66.lemma66_colNorm2 dAc j = columnFrob dA j := by
      simpa only [dAc] using
        higham19_lemma66_colNorm2_real_eq_columnFrob dA j
    have hcAc_eq : Lemma66.lemma66_colNorm2 cAc j =
        columnFrob (fun i k => cA * A i k) j := by
      simpa only [cAc] using
        higham19_lemma66_colNorm2_real_eq_columnFrob
          (fun i k => cA * A i k) j
    have hscaled :
        columnFrob (fun i k => cA * A i k) j =
          cA * columnFrob A j := by
      rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2,
        vecNorm2_smul, abs_of_nonneg hcA]
    rw [hdAc_eq, hcAc_eq, hscaled]
    exact hcol j
  have hentry : ∀ i j, |dA i j| ≤ cA * ∑ k : Fin n, |A k j| := by
    intro i j
    have h66 := Lemma66.lemma66_a_abs_entry_le dAc cAc hcAc_col i j
    simpa [dAc, cAc, Lemma66.lemma66_colNorm1, abs_mul,
      abs_of_nonneg hcA, Finset.mul_sum] using h66
  intro i
  have hres : b i - matMulVec n A xhat i = matMulVec n dA xhat i := by
    rw [← heq i]
    unfold matMulVec
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring
  rw [hres]
  calc
    |matMulVec n dA xhat i|
        ≤ ∑ j : Fin n, |dA i j| * |xhat j| :=
          abs_matMulVec_le n dA xhat i
    _ ≤ ∑ j : Fin n,
          (cA * ∑ k : Fin n, |A k j|) * |xhat j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)
    _ = cA * ∑ j : Fin n, (∑ k : Fin n, |A k j|) * |xhat j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Modular §19.7 residual adapter corresponding to the caller-supplied
Frobenius inverse bound, retained separately from the source-closing route. -/
theorem higham19_section19_7_actual_residual_bridge_nonzero_rhs_of_uniform_frob_inverse_bound
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b ≠ 0) (tau : ℝ) (htau : 0 ≤ tau)
    (hinverse : ∀ dQ : Fin n → Fin n → ℝ,
      frobNorm dQ ≤ higham19Theorem5RhsCoeff fp n →
      ∃ T : Fin n → Fin n → ℝ,
        (∀ i j, matMul n T
          (fun r k => fl_householderQR_Q fp n A k r + dQ k r) i j =
            idMatrix n i j) ∧
        frobNorm T ≤ tau) :
    ∀ i,
      |b i - matMulVec n A (fl_householderQR_solve fp n A b) i| ≤
        higham19Eq1914AbsorbCoeff fp n tau *
          ∑ j : Fin n, (∑ k : Fin n, |A k j|) *
            |fl_householderQR_solve fp n A b j| := by
  have heq14 :=
    higham19_eq19_14_actual_columnwise_nonzero_rhs_of_uniform_frob_inverse_bound
    fp n A b hn hvalid hdiag hb tau htau hinverse
  let K := householderConstructApplyGammaIndex n
  have hKpos : 0 < K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hnvalid : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hG : 0 ≤ gamma fp (n * K) := by
    simpa [K] using gamma_nonneg fp hvalid
  have hgn : 0 ≤ gamma fp n := gamma_nonneg fp hnvalid
  have hB : 0 ≤ higham19Theorem5RhsCoeff fp n := by
    simpa [higham19Theorem5RhsCoeff, K] using gamma_nonneg fp hvalid
  have hcoeff : 0 ≤ higham19Eq1914AbsorbCoeff fp n tau := by
    dsimp [higham19Eq1914AbsorbCoeff]
    exact add_nonneg hG
      (mul_nonneg (mul_nonneg htau (add_nonneg hB hgn)) (by linarith))
  exact higham19_section19_7_lemma66_residual_bridge heq14 hcoeff

/-- Actual-executor §19.7 residual bridge for nonzero `b`, using the
dimension-faithful equation-(19.14) coefficient derived from `B < 1`. -/
theorem higham19_section19_7_actual_residual_bridge_nonzero_rhs
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b ≠ 0)
    (hsmall : higham19Theorem5RhsCoeff fp n < 1) :
    ∀ i,
      |b i - matMulVec n A (fl_householderQR_solve fp n A b) i| ≤
        higham19Eq1914SourceCoeff fp n *
          ∑ j : Fin n, (∑ k : Fin n, |A k j|) *
            |fl_householderQR_solve fp n A b j| := by
  have heq14 := higham19_eq19_14_actual_columnwise_nonzero_rhs
    fp n A b hn hvalid hdiag hb hsmall
  let K := householderConstructApplyGammaIndex n
  let G := gamma fp (n * K)
  let gn := gamma fp n
  let B := higham19Theorem5RhsCoeff fp n
  have hKpos : 0 < K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hnvalid : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hG : 0 ≤ G := by
    simpa [G, K] using gamma_nonneg fp hvalid
  have hgn : 0 ≤ gn := by simpa [gn] using gamma_nonneg fp hnvalid
  have hB : 0 ≤ B := by
    simpa [B, higham19Theorem5RhsCoeff, K] using gamma_nonneg fp hvalid
  have htau : 0 ≤ 1 / (1 - B) :=
    (one_div_pos.mpr (sub_pos.mpr (by simpa [B] using hsmall))).le
  have hcoeff : 0 ≤ higham19Eq1914SourceCoeff fp n := by
    dsimp [higham19Eq1914SourceCoeff]
    exact add_nonneg hG
      (mul_nonneg (mul_nonneg htau (add_nonneg hB hgn)) (by linarith))
  exact higham19_section19_7_lemma66_residual_bridge heq14 hcoeff

/-- Actual-executor §19.7 residual bridge for `b = 0`; no inverse assumption
is required. -/
theorem higham19_section19_7_actual_residual_bridge_zero_rhs
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp
      (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hb : b = 0) :
    ∀ i,
      |b i - matMulVec n A (fl_householderQR_solve fp n A b) i| ≤
        higham19Theorem5MatrixCoeff fp n *
          ∑ j : Fin n, (∑ k : Fin n, |A k j|) *
            |fl_householderQR_solve fp n A b j| := by
  have heq14 := higham19_eq19_14_actual_columnwise_zero_rhs
    fp n A b hn hvalid hdiag hb
  let K := householderConstructApplyGammaIndex n
  have hKpos : 0 < K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hnvalid : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_mul_of_pos_right n hKpos)
      (by simpa [K] using hvalid)
  have hG : 0 ≤ gamma fp (n * K) := by
    simpa [K] using gamma_nonneg fp hvalid
  have hgn : 0 ≤ gamma fp n := gamma_nonneg fp hnvalid
  have hcoeff : 0 ≤ higham19Theorem5MatrixCoeff fp n := by
    dsimp [higham19Theorem5MatrixCoeff]
    exact add_nonneg hG (mul_nonneg hgn (by linarith))
  exact higham19_section19_7_lemma66_residual_bridge heq14 hcoeff

end NumStability
