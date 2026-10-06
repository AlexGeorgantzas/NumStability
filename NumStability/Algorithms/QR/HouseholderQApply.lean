-- Algorithms/QR/HouseholderQApply.lean
--
-- Rounded application of the stored Householder data from a QR panel.
-- The recursion applies the trailing reflectors first and the current
-- reflector last, so it computes the Q action without first forming Q.

import NumStability.Algorithms.QR.HouseholderQR

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Apply the Householder transformations retained by the zero-aware rounded
    QR panel algorithm directly to a vector.

    The active trailing transformations are replayed first.  The current
    reflector is then applied with the concrete rounded Householder kernel.
    Thus this is the reverse-reflector replay used to compute `Q * z`; it is
    not an exact multiplication by a separately formed rounded `Q`. -/
noncomputable def fl_householderQRPanel_applyQ (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _, _A, z => z
  | Nat.succ _, 0, _A, z => z
  | m + 1, p + 1, A, z =>
      let ytail : Fin m → ℝ :=
        fl_householderQRPanel_applyQ fp m p
          (fl_householderQRPanelNext fp A) (fun i => z i.succ)
      let w : Fin (m + 1) → ℝ := Fin.cons (z 0) ytail
      if _hcol : panelFirstColumn (Nat.succ_pos p) A = 0 then
        w
      else
        fl_householderApply fp (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 w

@[simp] theorem fl_householderQRPanel_applyQ_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) (z : Fin 0 → ℝ) :
    fl_householderQRPanel_applyQ fp 0 p A z = z := rfl

@[simp] theorem fl_householderQRPanel_applyQ_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ)
    (z : Fin (m + 1) → ℝ) :
    fl_householderQRPanel_applyQ fp (m + 1) 0 A z = z := rfl

@[simp] theorem fl_householderQRPanel_applyQ_succ_succ_zero
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (z : Fin (m + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z =
      Fin.cons (z 0)
        (fl_householderQRPanel_applyQ fp m p (trailingPanel A)
          (fun i => z i.succ)) := by
  simp [fl_householderQRPanel_applyQ, fl_householderQRPanelNext, hcol]

@[simp] theorem fl_householderQRPanel_applyQ_succ_succ_nonzero
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (z : Fin (m + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z =
      fl_householderApply fp (m + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1
        (Fin.cons (z 0)
          (fl_householderQRPanel_applyQ fp m p
            (fl_householderTrailingPanelStep fp A)
            (fun i => z i.succ))) := by
  simp [fl_householderQRPanel_applyQ, fl_householderQRPanelNext, hcol]

/-- Multiplication by a leading-one trailing-block embedding acts on a vector
    by preserving its leading component and multiplying its tail. -/
theorem matMulVec_embedTrailingOne_eq_finCons {m : ℕ}
    (U : Fin m → Fin m → ℝ) (z : Fin (m + 1) → ℝ) :
    matMulVec (m + 1) (embedTrailingOne U) z =
      Fin.cons (z 0) (matMulVec m U (fun i => z i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp
  · unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp

/-- Per-input fixed-reference certificate for direct rounded Householder replay.

    The explaining matrix `Q_hat` may depend on the input vector.  Its action
    is exactly the concrete replay output, and it lies in the stated Frobenius
    ball about the fixed exact QR factor. -/
structure HouseholderQRPanelApplyQFixedAccumulationCertificate
    (fp : FPModel) (m p : ℕ) (A : Fin m → Fin p → ℝ)
    (z : Fin m → ℝ) (etaQ : ℝ) where
  Q_hat : Fin m → Fin m → ℝ
  fixed :
    HouseholderQRPanelQhatFixedAccumError m
      (fl_householderQRPanel_Q fp m p A) Q_hat etaQ
  replay_eq :
    fl_householderQRPanel_applyQ fp m p A z = matMulVec m Q_hat z

/-- A direct-replay certificate is monotone in its accumulation radius. -/
def HouseholderQRPanelApplyQFixedAccumulationCertificate.mono
    {fp : FPModel} {m p : ℕ} {A : Fin m → Fin p → ℝ}
    {z : Fin m → ℝ} {etaQ etaQ' : ℝ}
    (h : HouseholderQRPanelApplyQFixedAccumulationCertificate
      fp m p A z etaQ)
    (heta : etaQ ≤ etaQ') :
    HouseholderQRPanelApplyQFixedAccumulationCertificate
      fp m p A z etaQ' :=
  { Q_hat := h.Q_hat
    fixed := h.fixed.mono heta
    replay_eq := h.replay_eq }

/-- One local direct-replay step satisfies the same matrix perturbation
    contract used by rounded accumulated-Q analysis.

    A zero active column performs an exact skip.  A nonzero active column uses
    the implementation-backed Householder construction/application theorem. -/
theorem fl_householderQRPanel_applyQ_step_error
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (z : Fin (m + 1) → ℝ)
    (hready : HouseholderQRPanelReady fp (m + 1) (p + 1) A) :
    let ytail : Fin m → ℝ :=
      fl_householderQRPanel_applyQ fp m p
        (fl_householderQRPanelNext fp A) (fun i => z i.succ)
    let w : Fin (m + 1) → ℝ := Fin.cons (z 0) ytail
    HouseholderAppError (m + 1)
      (householderQRPanel_Qhat_stepP A) w
      (fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z)
      (householderQRPanel_Qhat_stepCoeff fp A) := by
  dsimp only
  let ytail : Fin m → ℝ :=
    fl_householderQRPanel_applyQ fp m p
      (fl_householderQRPanelNext fp A) (fun i => z i.succ)
  let w : Fin (m + 1) → ℝ := Fin.cons (z 0) ytail
  change HouseholderAppError (m + 1)
    (householderQRPanel_Qhat_stepP A) w
    (fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z)
    (householderQRPanel_Qhat_stepCoeff fp A)
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
    refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
    · simpa [householderQRPanel_Qhat_stepP, hcol] using
        idMatrix_orthogonal (m + 1)
    · have hZ : frobNorm Z = 0 := by
        rw [frobNorm_eq_zero_iff]
        intro i j
        rfl
      rw [hZ]
      simp [householderQRPanel_Qhat_stepCoeff, hcol]
    · intro i
      have hid := congrFun (matMulVec_id (m + 1) w) i
      simpa [fl_householderQRPanel_applyQ, fl_householderQRPanelNext,
        householderQRPanel_Qhat_stepP, hcol, Z, w, ytail] using hid.symm
  · have hready' :=
      (HouseholderQRPanelReady_succ_succ_nonzero fp A hcol).mp hready
    have happ :=
      fl_householderConstructApply_appError fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A) w hcol hready'.1
    simpa [fl_householderQRPanel_applyQ, fl_householderQRPanelNext,
      householderQRPanel_Qhat_stepP, householderQRPanel_Qhat_stepCoeff,
      householderConstructApplyBound, hcol, w, ytail] using happ

/-- Direct reverse-reflector replay is an action by an input-dependent matrix
    within the closed accumulated-Q radius of the fixed exact QR factor. -/
noncomputable def fl_householderQRPanel_applyQ_fixed_Q_closed_accum_error
    (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (z : Fin m → ℝ),
      HouseholderQRPanelReady fp m p A →
      HouseholderQRPanelApplyQFixedAccumulationCertificate fp m p A z
        (householderQRPanel_QhatClosedBound fp m p A) := by
  intro m
  induction m with
  | zero =>
      intro p A z _hready
      let Z : Fin 0 → Fin 0 → ℝ := fun i _ => Fin.elim0 i
      refine
        { Q_hat := idMatrix 0
          fixed := ?_
          replay_eq := ?_ }
      · refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
        · simpa [fl_householderQRPanel_Q] using idMatrix_orthogonal 0
        · intro i
          exact Fin.elim0 i
        · have hZ : frobNorm Z = 0 := by
            rw [frobNorm_eq_zero_iff]
            intro i
            exact Fin.elim0 i
          simp [householderQRPanel_QhatClosedBound, Z, hZ]
      · funext i
        exact Fin.elim0 i
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A z _hready
          let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
          refine
            { Q_hat := idMatrix (m + 1)
              fixed := ?_
              replay_eq := ?_ }
          · refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
            · simpa [fl_householderQRPanel_Q] using
                idMatrix_orthogonal (m + 1)
            · intro i j
              simp [fl_householderQRPanel_Q, Z]
            · have hZ : frobNorm Z = 0 := by
                rw [frobNorm_eq_zero_iff]
                intro i j
                rfl
              simp [householderQRPanel_QhatClosedBound, Z, hZ]
          · simpa [fl_householderQRPanel_applyQ] using
              (matMulVec_id (m + 1) z).symm
      | succ p =>
          intro A z hready
          have htailReady :
              HouseholderQRPanelReady fp m p
                (fl_householderQRPanelNext fp A) := by
            by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
            · have ht :=
                (HouseholderQRPanelReady_succ_succ_zero fp A hcol).mp hready
              simpa [fl_householderQRPanelNext, hcol] using ht
            · have ht :=
                ((HouseholderQRPanelReady_succ_succ_nonzero fp A hcol).mp
                  hready).2
              simpa [fl_householderQRPanelNext, hcol] using ht
          let ztail : Fin m → ℝ := fun i => z i.succ
          have hTail :=
            ih p (fl_householderQRPanelNext fp A) ztail htailReady
          have hApp :=
            fl_householderQRPanel_applyQ_step_error fp A z hready
          let DeltaP : Fin (m + 1) → Fin (m + 1) → ℝ :=
            Classical.choose hApp.pert
          have hDeltaP :
              frobNorm DeltaP ≤ householderQRPanel_Qhat_stepCoeff fp A :=
            (Classical.choose_spec hApp.pert).1
          have hact :
              ∀ i : Fin (m + 1),
                fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z i =
                  matMulVec (m + 1)
                    (fun a b =>
                      householderQRPanel_Qhat_stepP A a b + DeltaP a b)
                    (Fin.cons (z 0)
                      (fl_householderQRPanel_applyQ fp m p
                        (fl_householderQRPanelNext fp A)
                        (fun i => z i.succ))) i :=
            (Classical.choose_spec hApp.pert).2
          let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
            householderQRPanel_Qhat_stepP A
          let c : ℝ := householderQRPanel_Qhat_stepCoeff fp A
          let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
            embedTrailingOne hTail.Q_hat
          let Q_hat : Fin (m + 1) → Fin (m + 1) → ℝ :=
            matMul (m + 1) (fun a b => P a b + DeltaP a b) B
          let E : Fin (m + 1) → Fin (m + 1) → ℝ :=
            matMul (m + 1) DeltaP B
          have hc : 0 ≤ c := by
            exact le_trans (frobNorm_nonneg DeltaP) (by simpa [c] using hDeltaP)
          have hP : IsOrthogonal (m + 1) P := by
            simpa [P] using hApp.orth
          have hResidual :
              ∃ E0 : Fin (m + 1) → Fin (m + 1) → ℝ,
                (∀ i j : Fin (m + 1),
                  Q_hat i j =
                    matMulRect (m + 1) (m + 1) (m + 1) P B i j +
                      E0 i j) ∧
                frobNorm E0 ≤ c * frobNorm B := by
            refine ⟨E, ?_, ?_⟩
            · intro i j
              have hdist := congrFun
                (congrFun (matMul_add_left (m + 1) P DeltaP B) i) j
              simpa [Q_hat, E, matMulRect, matMul] using hdist
            · calc
                frobNorm E ≤ frobNorm DeltaP * frobNorm B := by
                  simpa [E] using frobNorm_matMul_le DeltaP B
                _ ≤ c * frobNorm B := by
                  exact mul_le_mul_of_nonneg_right
                    (by simpa [c] using hDeltaP) (frobNorm_nonneg B)
          have hQref :
              fl_householderQRPanel_Q fp (m + 1) (p + 1) A =
                matMul (m + 1) P
                  (embedTrailingOne
                    (fl_householderQRPanel_Q fp m p
                      (fl_householderQRPanelNext fp A))) := by
            simpa [P] using
              fl_householderQRPanel_Q_succ_succ_as_stepP fp A
          have hFixedRaw :=
            HouseholderQRPanelQhatFixedAccumError.cons_closed hTail.fixed
              P (fl_householderQRPanel_Q fp (m + 1) (p + 1) A)
              Q_hat c hP hc hQref (by simpa [B] using hResidual)
          have hFixed :
              HouseholderQRPanelQhatFixedAccumError (m + 1)
                (fl_householderQRPanel_Q fp (m + 1) (p + 1) A)
                Q_hat
                (householderQRPanel_QhatClosedBound fp
                  (m + 1) (p + 1) A) := by
            simpa [householderQRPanel_QhatClosedBound, c] using hFixedRaw
          let w : Fin (m + 1) → ℝ :=
            Fin.cons (z 0)
              (fl_householderQRPanel_applyQ fp m p
                (fl_householderQRPanelNext fp A) ztail)
          have hw : w = matMulVec (m + 1) B z := by
            dsimp [w]
            rw [hTail.replay_eq]
            simpa [B, ztail] using
              (matMulVec_embedTrailingOne_eq_finCons hTail.Q_hat z).symm
          refine
            { Q_hat := Q_hat
              fixed := hFixed
              replay_eq := ?_ }
          funext i
          calc
            fl_householderQRPanel_applyQ fp (m + 1) (p + 1) A z i =
                matMulVec (m + 1)
                  (fun a b => P a b + DeltaP a b) w i := by
              simpa [P, w, ztail] using hact i
            _ = matMulVec (m + 1)
                (fun a b => P a b + DeltaP a b)
                (matMulVec (m + 1) B z) i := by rw [hw]
            _ = matMulVec (m + 1) Q_hat z i := by
              simpa [Q_hat] using
                (matMulVec_matMul (m + 1)
                  (fun a b => P a b + DeltaP a b) B z i).symm

/-- The branch-sensitive replay radius is bounded by a uniform recurrence whose
    step count is the panel's number of columns.

    For an `N x p` panel this records at most `p` Householder applications,
    rather than the ambient row count `N`. -/
theorem householderQRPanel_QhatClosedBound_le_uniform_cols
    (fp : FPModel) :
    ∀ (p m N : ℕ) (A : Fin m → Fin p → ℝ),
      m ≤ N →
      gammaValid fp (11 * N + 23) →
      householderQRPanel_QhatClosedBound fp m p A ≤
        householderQR_QhatUniformClosedBound fp N p := by
  intro p
  induction p with
  | zero =>
      intro m N A _hmN _hvalid
      cases m with
      | zero =>
          simp [householderQRPanel_QhatClosedBound,
            householderQR_QhatUniformClosedBound]
      | succ m =>
          simp [householderQRPanel_QhatClosedBound,
            householderQR_QhatUniformClosedBound]
  | succ p ih =>
      intro m N A hmN hvalid
      cases m with
      | zero =>
          simpa [householderQRPanel_QhatClosedBound] using
            householderQR_QhatUniformClosedBound_nonneg fp N hvalid (p + 1)
      | succ m =>
          let eta : ℝ :=
            householderQRPanel_QhatClosedBound fp m p
              (fl_householderQRPanelNext fp A)
          let U : ℝ := householderQR_QhatUniformClosedBound fp N p
          let a : ℝ := householderQRPanel_Qhat_stepCoeff fp A
          let c : ℝ := householderConstructApplyBound fp N
          let s : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ)
          let B : ℝ := Real.sqrt (N : ℝ)
          have hetaU : eta ≤ U :=
            ih m N (fl_householderQRPanelNext fp A) (by omega) hvalid
          have heta_nonneg : 0 ≤ eta :=
            householderQRPanel_QhatClosedBound_nonneg_of_global_gammaValid
              fp m p N (fl_householderQRPanelNext fp A) (by omega) hvalid
          have ha_nonneg : 0 ≤ a := by
            have hstepValid : gammaValid fp (11 * (m + 1) + 23) :=
              gammaValid_mono fp (by omega) hvalid
            simpa [a] using
              householderQRPanel_Qhat_stepCoeff_nonneg fp A hstepValid
          have ha_le_c : a ≤ c := by
            simpa [a, c] using
              householderQRPanel_Qhat_stepCoeff_le_global fp A hmN hvalid
          have hc_nonneg : 0 ≤ c := by
            simpa [c] using
              householderConstructApplyBound_nonneg fp N hvalid
          have hs_le_B : s ≤ B := by
            have hcast : ((m + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast hmN
            simpa [s, B] using Real.sqrt_le_sqrt hcast
          have hterm : s + eta ≤ B + U := add_le_add hs_le_B hetaU
          have hterm_nonneg : 0 ≤ s + eta := by
            exact add_nonneg (Real.sqrt_nonneg _) heta_nonneg
          have hmul : a * (s + eta) ≤ c * (B + U) := by
            have h1 : a * (s + eta) ≤ c * (s + eta) :=
              mul_le_mul_of_nonneg_right ha_le_c hterm_nonneg
            have h2 : c * (s + eta) ≤ c * (B + U) :=
              mul_le_mul_of_nonneg_left hterm hc_nonneg
            exact le_trans h1 h2
          simpa [householderQRPanel_QhatClosedBound,
            householderQR_QhatUniformClosedBound,
            eta, U, a, c, s, B] using add_le_add hetaU hmul

/-- Global-gamma wrapper for direct replay with the source-facing column-count
    recurrence. -/
noncomputable def fl_householderQRPanel_applyQ_fixed_Q_uniform_cols_accum_error
    (fp : FPModel) (m p N : ℕ) (A : Fin m → Fin p → ℝ)
    (z : Fin m → ℝ) (hmN : m ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    HouseholderQRPanelApplyQFixedAccumulationCertificate fp m p A z
      (householderQR_QhatUniformClosedBound fp N p) := by
  have hready : HouseholderQRPanelReady fp m p A :=
    HouseholderQRPanelReady_of_global_gammaValid fp m p N A hmN hvalid
  have hclosed :=
    fl_householderQRPanel_applyQ_fixed_Q_closed_accum_error
      fp m p A z hready
  exact hclosed.mono
    (householderQRPanel_QhatClosedBound_le_uniform_cols
      fp p m N A hmN hvalid)

/-- Closed-form source-facing replay radius with one factor per panel column. -/
noncomputable def fl_householderQRPanel_applyQ_fixed_Q_closed_form_cols_accum_error
    (fp : FPModel) (m p N : ℕ) (A : Fin m → Fin p → ℝ)
    (z : Fin m → ℝ) (hmN : m ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    HouseholderQRPanelApplyQFixedAccumulationCertificate fp m p A z
      (householderQR_QhatClosedFormBound fp N p) := by
  simpa [householderQR_QhatUniformClosedBound_eq_closedForm] using
    fl_householderQRPanel_applyQ_fixed_Q_uniform_cols_accum_error
      fp m p N A z hmN hvalid

/-- Simpler source-facing growth bound for direct replay.  Its leading factor
    is the panel column count, which is the number of replayed reflectors. -/
noncomputable def fl_householderQRPanel_applyQ_fixed_Q_growth_cols_accum_error
    (fp : FPModel) (m p N : ℕ) (A : Fin m → Fin p → ℝ)
    (z : Fin m → ℝ) (hmN : m ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    HouseholderQRPanelApplyQFixedAccumulationCertificate fp m p A z
      ((p : ℝ) * householderConstructApplyBound fp N *
        (1 + householderConstructApplyBound fp N) ^ p *
        Real.sqrt (N : ℝ)) := by
  have hclosed :=
    fl_householderQRPanel_applyQ_fixed_Q_closed_form_cols_accum_error
      fp m p N A z hmN hvalid
  exact hclosed.mono
    (householderQR_QhatClosedFormBound_le_growth fp N p hvalid)

end NumStability
