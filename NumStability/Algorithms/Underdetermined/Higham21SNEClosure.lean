-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete Householder-QR closure for the seminormal-equations path.

import NumStability.Algorithms.Underdetermined.Higham21SNESigned
import NumStability.Algorithms.Underdetermined.Higham21SNEEnvelopeTransfer
import NumStability.Algorithms.Underdetermined.Higham21SNEQRMajorant
import NumStability.Algorithms.Underdetermined.Higham21SNERemainderBounds
import NumStability.Algorithms.Underdetermined.Higham21SNEConditionTransfer

namespace NumStability

open scoped BigOperators

/-!
# Concrete signed SNE closure

The analysis-only QR perturbation below is chosen from the proved
implementation-backed Householder panel theorem.  The computed objects remain
the actual panel `Q`, its actual top square `R_hat`, the two rounded triangular
solves, and the rounded final `A^T` action.
-/

/-- The exact orthogonal witness returned by the concrete Householder panel. -/
noncomputable def higham21SNEHouseholderQFull
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin (m + k) -> Real :=
  fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)

/-- The actual tall factor returned by the concrete Householder panel. -/
noncomputable def higham21SNEHouseholderRTall
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)

/-- The actual square top block used by both rounded SNE triangular solves. -/
noncomputable def higham21SNEHouseholderRHat
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) : Fin m -> Fin m -> Real :=
  fun i j => higham21SNEHouseholderRTall fp A (Fin.castAdd k i) j

/-- The first `m` columns of the exact full Householder witness. -/
noncomputable def higham21SNEHouseholderEconomyQ
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fun i j => higham21SNEHouseholderQFull fp A i (Fin.castAdd k j)

/-- A canonical analysis-only QR backward perturbation for the concrete panel.

It is selected from Higham Theorem 19.4; it is not a computed quantity. -/
noncomputable def higham21SNEHouseholderDeltaAT
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    Fin (m + k) -> Fin m -> Real :=
  Classical.choose
    ((H19.Theorem19_4.householder_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k)
        hvalidQR).result)

/-- The row-oriented form of the canonical QR perturbation. -/
noncomputable def higham21SNEHouseholderDeltaA
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    Fin m -> Fin (m + k) -> Real :=
  finiteTranspose (higham21SNEHouseholderDeltaAT fp A hm hvalidQR)

/-- The nonnegative Frobenius-unit majorant used to expose the componentwise
form of the concrete Householder QR backward error. -/
noncomputable def higham21SNEHouseholderG {m k : Nat} :
    Fin (m + k) -> Fin (m + k) -> Real :=
  highamHouseholderG (m + k)

/-- The componentwise coefficient attached to the concrete Householder QR
perturbation.  The factor `m+k` converts the proved columnwise Euclidean
bound into Higham's `G |A|` form. -/
noncomputable def higham21SNEHouseholderRho
    (fp : FPModel) (m k : Nat) : Real :=
  (m + k : Real) * H19.Theorem19_4.gamma_tilde fp (m + k) m

theorem higham21_sne_householder_deltaAT_spec
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    (forall i j,
      finiteTranspose A i j +
          higham21SNEHouseholderDeltaAT fp A hm hvalidQR i j =
        matMulRect (m + k) (m + k) m
          (higham21SNEHouseholderQFull fp A)
          (higham21SNEHouseholderRTall fp A) i j) /\
    (forall j,
      columnFrob (higham21SNEHouseholderDeltaAT fp A hm hvalidQR) j <=
        H19.Theorem19_4.gamma_tilde fp (m + k) m *
          columnFrob (finiteTranspose A) j) := by
  have hQR := H19.Theorem19_4.householder_qr_backward_error
    fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR
  simpa [higham21SNEHouseholderDeltaAT,
    higham21SNEHouseholderQFull, higham21SNEHouseholderRTall] using
      (Classical.choose_spec hQR.result)

theorem higham21_sne_householder_QFull_orthogonal
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    IsOrthogonal (m + k) (higham21SNEHouseholderQFull fp A) := by
  simpa [higham21SNEHouseholderQFull] using
    (H19.Theorem19_4.householder_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k)
        hvalidQR).orth

theorem higham21_sne_householder_RTall_upper
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    IsUpperTrapezoidal (m + k) m
      (higham21SNEHouseholderRTall fp A) := by
  simpa [higham21SNEHouseholderRTall] using
    (H19.Theorem19_4.householder_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k)
        hvalidQR).upper

/-- The economy part of the exact full Householder witness has orthonormal
columns. -/
theorem higham21_sne_householder_economyQ_orthonormal
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    GramSchmidtOrthonormalColumns
      (higham21SNEHouseholderEconomyQ fp A) := by
  have hQ := higham21_sne_householder_QFull_orthogonal
    fp A hm hvalidQR
  intro i j
  simpa [higham21SNEHouseholderEconomyQ,
    GramSchmidtOrthonormalColumns, rectangularGram, idMatrix] using
      hQ.col_orthonormal (Fin.castAdd k i) (Fin.castAdd k j)

/-- The concrete QR perturbation, economy witness, and actual top factor obey
the exact factorization required by the signed SNE analysis. -/
theorem higham21_sne_householder_economy_factor
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    finiteTranspose
        (fun i j => A i j +
          higham21SNEHouseholderDeltaA fp A hm hvalidQR i j) =
      rectMatMul (higham21SNEHouseholderEconomyQ fp A)
        (higham21SNEHouseholderRHat fp A) := by
  have hspec :=
    (higham21_sne_householder_deltaAT_spec fp A hm hvalidQR).1
  have hupper := higham21_sne_householder_RTall_upper fp A hm hvalidQR
  have hblock :
      higham21SNEHouseholderRTall fp A =
        lsQRTallBlock (k := k) (higham21SNEHouseholderRHat fp A) := by
    simpa [higham21SNEHouseholderRHat] using
      lsQRTallBlock_of_upper_trapezoidal
        (higham21SNEHouseholderRTall fp A) hupper
  ext i j
  change
    finiteTranspose A i j +
        higham21SNEHouseholderDeltaAT fp A hm hvalidQR i j =
      rectMatMul (higham21SNEHouseholderEconomyQ fp A)
        (higham21SNEHouseholderRHat fp A) i j
  rw [hspec i j]
  rw [hblock]
  unfold matMulRect rectMatMul
  rw [Fin.sum_univ_add]
  simp [lsQRTallBlock, higham21SNEHouseholderEconomyQ]

/-- Columnwise Theorem 19.4 control, transposed to the rowwise perturbation
used in Chapter 21. -/
theorem higham21_sne_householder_deltaA_rowwise
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    forall i,
      rectRowNorm2 (higham21SNEHouseholderDeltaA fp A hm hvalidQR) i <=
        H19.Theorem19_4.gamma_tilde fp (m + k) m * rectRowNorm2 A i := by
  exact higham21_row_bounds_of_transposed_qr_column_bounds
    (finiteTranspose A)
    (higham21SNEHouseholderDeltaAT fp A hm hvalidQR)
    (higham21_sne_householder_deltaAT_spec fp A hm hvalidQR).2

/-- The canonical analysis perturbation selected above satisfies the
componentwise Higham Householder certificate with the explicit uniform
majorant `G = (m+k)^{-1} ee^T`. -/
theorem higham21_sne_householder_deltaA_componentwise
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    forall p i,
      |higham21SNEHouseholderDeltaA fp A hm hvalidQR i p| <=
        higham21SNEHouseholderRho fp m k *
          (∑ s : Fin (m + k),
            higham21SNEHouseholderG p s * |A i s|) := by
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  have heta : 0 <= eta := by
    simpa [eta] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  intro p i
  have hcol :=
    (higham21_sne_householder_deltaAT_spec fp A hm hvalidQR).2 i
  have hl1 :=
    columnFrob_le_abs_column_sum (finiteTranspose A) i
  have hG :=
    card_mul_highamHouseholderG_mul_abs_col
      hn (finiteTranspose A) p i
  calc
    |higham21SNEHouseholderDeltaA fp A hm hvalidQR i p| =
        |higham21SNEHouseholderDeltaAT fp A hm hvalidQR p i| := by rfl
    _ <= columnFrob
        (higham21SNEHouseholderDeltaAT fp A hm hvalidQR) i :=
      abs_entry_le_columnFrob
        (higham21SNEHouseholderDeltaAT fp A hm hvalidQR) p i
    _ <= eta * columnFrob (finiteTranspose A) i := by
      simpa [eta] using hcol
    _ <= eta * (∑ s : Fin (m + k), |finiteTranspose A s i|) :=
      mul_le_mul_of_nonneg_left hl1 heta
    _ = higham21SNEHouseholderRho fp m k *
          (∑ s : Fin (m + k),
            higham21SNEHouseholderG p s * |A i s|) := by
      rw [show (∑ s : Fin (m + k),
            higham21SNEHouseholderG p s * |A i s|) =
          matMulRect (m + k) (m + k) m
            (highamHouseholderG (m + k))
            (fun a b => |finiteTranspose A a b|) p i by rfl]
      rw [<- hG]
      simp only [higham21SNEHouseholderRho, eta, Nat.cast_add]
      ring

/-- The same canonical perturbation retains the sharp columnwise coefficient
after aggregation to a rectangular Frobenius bound. -/
theorem higham21_sne_householder_deltaA_frobNorm
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    frobNorm (higham21SNEHouseholderDeltaA fp A hm hvalidQR) <=
      H19.Theorem19_4.gamma_tilde fp (m + k) m * frobNorm A := by
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let dAT := higham21SNEHouseholderDeltaAT fp A hm hvalidQR
  have heta : 0 <= eta := by
    simpa [eta] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrect : frobNormRect dAT <= eta * frobNormRect (finiteTranspose A) := by
    apply frobNormRect_le_of_col_vecNorm2_le dAT (finiteTranspose A) heta
    intro j
    simpa [dAT, eta, columnFrob_eq_vecNorm2] using
      (higham21_sne_householder_deltaAT_spec fp A hm hvalidQR).2 j
  calc
    frobNorm (higham21SNEHouseholderDeltaA fp A hm hvalidQR) =
        frobNormRect (higham21SNEHouseholderDeltaA fp A hm hvalidQR) :=
      (frobNormRect_eq_frobNormFn _).symm
    _ = frobNormRect dAT := by
      simpa [higham21SNEHouseholderDeltaA, dAT] using
        frobNormRect_finiteTranspose dAT
    _ <= eta * frobNormRect (finiteTranspose A) := hrect
    _ = eta * frobNormRect A := by
      rw [frobNormRect_finiteTranspose]
    _ = H19.Theorem19_4.gamma_tilde fp (m + k) m * frobNorm A := by
      rw [frobNormRect_eq_frobNormFn]

theorem higham21_sne_householder_G_nonneg
    {m k : Nat} (hm : 0 < m) :
    forall p s, 0 <= (higham21SNEHouseholderG :
      Fin (m + k) -> Fin (m + k) -> Real) p s := by
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  simpa [higham21SNEHouseholderG] using highamHouseholderG_nonneg hn

theorem higham21_sne_householder_G_rectOpNorm2Le_one
    {m k : Nat} (hm : 0 < m) :
    rectOpNorm2Le
      (higham21SNEHouseholderG :
        Fin (m + k) -> Fin (m + k) -> Real) 1 := by
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  apply opNorm2Le_to_rectOpNorm2Le
  apply opNorm2Le_of_frobNorm_le
  rw [higham21SNEHouseholderG, highamHouseholderG_frobNorm hn]

theorem higham21_sne_householder_rho_nonneg
    (fp : FPModel) {m k : Nat}
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    0 <= higham21SNEHouseholderRho fp m k := by
  exact mul_nonneg (by positivity)
    (H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR)

/-- Moving the dual vector from `ybar` to `yhat` costs at most the
Frobenius action of `A` on their difference. -/
theorem higham21_sne_source_dual_action_at_perturbed_vector
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNormRect A * vecNorm2 (fun i => ybar i - yhat i) := by
  let d : Fin m -> Real := fun i => ybar i - yhat i
  let what : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)
  let wbar : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wd : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |d i|)
  have hwhat : forall j, 0 <= what j := by
    intro j
    dsimp [what, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwbar : forall j, 0 <= wbar j := by
    intro j
    dsimp [wbar, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwdnonneg : forall j, 0 <= wd j := by
    intro j
    dsimp [wd, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpoint : forall j, |what j| <= wbar j + wd j := by
    intro j
    rw [abs_of_nonneg (hwhat j)]
    dsimp [what, wbar, wd, d, rectTransposeMulVec, absMatrixRect]
    calc
      ∑ i : Fin m, |A i j| * |yhat i| <=
          ∑ i : Fin m,
            |A i j| * (|ybar i| + |ybar i - yhat i|) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc
          |yhat i| = |ybar i - (ybar i - yhat i)| := by
            congr 1
            ring
          _ <= |ybar i| + |ybar i - yhat i| := abs_sub _ _
      _ = (∑ i : Fin m, |A i j| * |ybar i|) +
          ∑ i : Fin m, |A i j| * |ybar i - yhat i| := by
        rw [<- Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmajor : vecNorm2 what <= vecNorm2 (fun j => wbar j + wd j) := by
    apply vecNorm2_le_of_abs_le
    intro j
    simpa [abs_of_nonneg (add_nonneg (hwbar j) (hwdnonneg j))] using
      hpoint j
  have hwd : vecNorm2 wd <= frobNormRect A * vecNorm2 d := by
    calc
      vecNorm2 wd =
          vecNorm2
            (rectMatMulVec (finiteTranspose (absMatrixRect A))
              (fun i => |d i|)) := by rfl
      _ <= frobNormRect (finiteTranspose (absMatrixRect A)) *
          vecNorm2 (fun i => |d i|) :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul _ _
      _ = frobNormRect A * vecNorm2 d := by
        rw [frobNormRect_finiteTranspose]
        rw [show frobNormRect (absMatrixRect A) = frobNormRect A by
          simpa [absMatrixRect] using frobNormRect_abs A]
        rw [vecNorm2_abs]
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) =
      vecNorm2 what := by rfl
    _ <= vecNorm2 (fun j => wbar j + wd j) := hmajor
    _ <= vecNorm2 wbar + vecNorm2 wd := vecNorm2_add_le wbar wd
    _ <= vecNorm2 wbar + frobNormRect A * vecNorm2 d :=
      add_le_add le_rfl hwd
    _ = vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNormRect A * vecNorm2 (fun i => ybar i - yhat i) := by rfl

/-- A sharper leading/quadratic split for final formation: the leading
coefficient remains the actual matrix-vector coefficient `gamma`, while a
master radius `theta` dominates only the genuinely quadratic products. -/
theorem higham21_sne_formation_error_le_gamma_plus_uniform_quadratic
    {m n : Nat}
    (theta rho gamma Kd q : Real)
    (htheta : 0 <= theta)
    (hrho : 0 <= rho) (hrho_theta : rho <= theta) (hrho_lt : rho < 1)
    (hgamma : 0 <= gamma) (hgamma_theta : gamma <= theta)
    (hKd : 0 <= Kd) (hq : 0 <= q)
    (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) (g : Fin n -> Real)
    (hFormation :
      vecNorm2 g <= gamma *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)))
    (hbar :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
        q / (1 - rho))
    (hd : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd) :
    vecNorm2 g <=
      gamma * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hqdiv : 0 <= q / (1 - rho) := div_nonneg hq hden.le
  have hA : 0 <= frobNorm A := frobNorm_nonneg A
  have hsource := higham21_sne_source_abs_action_change A ybar yhat
  have hhat :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        q / (1 - rho) + frobNorm A * (theta * Kd) := by
    exact hsource.trans (add_le_add hbar
      (mul_le_mul_of_nonneg_left hd hA))
  have hgammaBound : vecNorm2 g <=
      gamma * (q / (1 - rho) + frobNorm A * (theta * Kd)) := by
    exact hFormation.trans
      (mul_le_mul_of_nonneg_left hhat hgamma)
  have hgammaRho : gamma * rho <= theta ^ 2 := by
    calc
      gamma * rho <= theta * rho :=
        mul_le_mul_of_nonneg_right hgamma_theta hrho
      _ <= theta * theta :=
        mul_le_mul_of_nonneg_left hrho_theta htheta
      _ = theta ^ 2 := by ring
  have hgammaTheta : gamma * theta <= theta ^ 2 := by
    calc
      gamma * theta <= theta * theta :=
        mul_le_mul_of_nonneg_right hgamma_theta htheta
      _ = theta ^ 2 := by ring
  have hidentity : q / (1 - rho) = q + rho * (q / (1 - rho)) := by
    field_simp [ne_of_gt hden]
    ring
  have hsplit : gamma * (q / (1 - rho)) <=
      gamma * q + theta ^ 2 * (q / (1 - rho)) := by
    calc
      gamma * (q / (1 - rho)) =
          gamma * (q + rho * (q / (1 - rho))) :=
        congrArg (fun z => gamma * z) hidentity
      _ =
          gamma * q + (gamma * rho) * (q / (1 - rho)) := by ring
      _ <= gamma * q + theta ^ 2 * (q / (1 - rho)) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hgammaRho hqdiv)
  have hdiffFormation :
      gamma * (frobNorm A * (theta * Kd)) <=
        theta ^ 2 * (frobNorm A * Kd) := by
    calc
      gamma * (frobNorm A * (theta * Kd)) =
          (gamma * theta) * (frobNorm A * Kd) := by ring
      _ <= theta ^ 2 * (frobNorm A * Kd) :=
        mul_le_mul_of_nonneg_right hgammaTheta (mul_nonneg hA hKd)
  calc
    vecNorm2 g <=
        gamma * (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
      hgammaBound
    _ = gamma * (q / (1 - rho)) +
        gamma * (frobNorm A * (theta * Kd)) := by ring
    _ <= (gamma * q + theta ^ 2 * (q / (1 - rho))) +
        theta ^ 2 * (frobNorm A * Kd) :=
      add_le_add hsplit hdiffFormation
    _ = gamma * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by ring

/-- A direct Frobenius bound for the Gram displacement generated by a
rectangular perturbation. -/
theorem higham21_sne_rectGram_difference_frobNorm_le
    {m n : Nat} (A F : Fin m -> Fin n -> Real) :
    frobNorm (fun i j =>
        rectGram (fun r s => A r s + F r s) i j - rectGram A i j) <=
      2 * frobNorm A * frobNorm F + frobNorm F ^ 2 := by
  let AFt : Fin m -> Fin m -> Real := rectMatMul A (finiteTranspose F)
  let FAt : Fin m -> Fin m -> Real := rectMatMul F (finiteTranspose A)
  let FFt : Fin m -> Fin m -> Real := rectMatMul F (finiteTranspose F)
  have hdecomp :
      (fun i j =>
        rectGram (fun r s => A r s + F r s) i j - rectGram A i j) =
      fun i j => AFt i j + FAt i j + FFt i j := by
    ext i j
    dsimp [AFt, FAt, FFt, rectGram, rectMatMul, finiteTranspose]
    rw [<- Finset.sum_sub_distrib]
    rw [<- Finset.sum_add_distrib]
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hAFt : frobNorm AFt <= frobNorm A * frobNorm F := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect AFt <=
          frobNormRect A * frobNormRect (finiteTranspose F) := by
        simpa [AFt] using
          frobNormRect_rectMatMul_le A (finiteTranspose F)
      _ = frobNorm A * frobNorm F := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  have hFAt : frobNorm FAt <= frobNorm F * frobNorm A := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect FAt <=
          frobNormRect F * frobNormRect (finiteTranspose A) := by
        simpa [FAt] using
          frobNormRect_rectMatMul_le F (finiteTranspose A)
      _ = frobNorm F * frobNorm A := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  have hFFt : frobNorm FFt <= frobNorm F * frobNorm F := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect FFt <=
          frobNormRect F * frobNormRect (finiteTranspose F) := by
        simpa [FFt] using
          frobNormRect_rectMatMul_le F (finiteTranspose F)
      _ = frobNorm F * frobNorm F := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn]
  rw [hdecomp]
  calc
    frobNorm (fun i j => AFt i j + FAt i j + FFt i j) <=
        frobNorm (fun i j => AFt i j + FAt i j) + frobNorm FFt :=
      frobNorm_add_le _ _
    _ <= (frobNorm AFt + frobNorm FAt) + frobNorm FFt :=
      add_le_add (frobNorm_add_le AFt FAt) le_rfl
    _ <= (frobNorm A * frobNorm F + frobNorm F * frobNorm A) +
        frobNorm F * frobNorm F :=
      add_le_add (add_le_add hAFt hFAt) hFFt
    _ = 2 * frobNorm A * frobNorm F + frobNorm F ^ 2 := by ring

/-- Resolvent identity in Frobenius norm, stated only with two-sided inverse
certificates. -/
theorem higham21_sne_inverse_difference_frobNorm_le
    {m : Nat}
    (S T G H : Fin m -> Fin m -> Real)
    (hS : IsInverse m S G) (hT : IsInverse m T H) :
    frobNorm (fun i j => H i j - G i j) <=
      frobNorm G * frobNorm (fun i j => S i j - T i j) * frobNorm H := by
  let E : Fin m -> Fin m -> Real := fun i j => S i j - T i j
  have hGS : rectMatMul G S = idMatrix m := by
    ext i j
    exact hS.1 i j
  have hTH : rectMatMul T H = idMatrix m := by
    ext i j
    exact hT.2 i j
  have hresolvent :
      (fun i j => H i j - G i j) = rectMatMul (rectMatMul G E) H := by
    calc
      (fun i j => H i j - G i j) =
          fun i j =>
            rectMatMul (rectMatMul G S) H i j -
              rectMatMul G (rectMatMul T H) i j := by
        rw [hGS, hTH]
        rw [rectMatMul_id_left, rectMatMul_id_right]
      _ = fun i j =>
          rectMatMul G (rectMatMul S H) i j -
            rectMatMul G (rectMatMul T H) i j := by
        rw [rectMatMul_assoc G S H]
      _ = rectMatMul G
          (fun i j => rectMatMul S H i j - rectMatMul T H i j) := by
        symm
        exact rectMatMul_sub_right G (rectMatMul S H) (rectMatMul T H)
      _ = rectMatMul G (rectMatMul E H) := by
        rw [show rectMatMul E H =
            (fun i j => rectMatMul S H i j - rectMatMul T H i j) by
          simpa [E] using rectMatMul_sub_left S T H]
      _ = rectMatMul (rectMatMul G E) H := by
        exact (rectMatMul_assoc G E H).symm
  rw [hresolvent]
  calc
    frobNorm (rectMatMul (rectMatMul G E) H) <=
        frobNorm (rectMatMul G E) * frobNorm H :=
      frobNorm_matMul_le (rectMatMul G E) H
    _ <= (frobNorm G * frobNorm E) * frobNorm H :=
      mul_le_mul_of_nonneg_right
        (frobNorm_matMul_le G E) (frobNorm_nonneg H)
    _ = frobNorm G * frobNorm (fun i j => S i j - T i j) *
        frobNorm H := by rfl

/-- A variant of the finite signed output theorem which leaves the QR action
and final-formation contributions as separate local radii.  This is useful for
an actual algorithm, whose two roundoff coefficients need not be identical. -/
theorem higham21_dh1993_signed_output_bound_separate
    {m n : Nat} (hm : 0 < m)
    (theta EF Eg ER : Real)
    (htheta : 0 <= theta)
    (A F : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv DeltaR1 DeltaR2 : Fin m -> Fin m -> Real)
    (ybar yhat : Fin m -> Real) (xbar : Fin n -> Real)
    (g : Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor :
      finiteTranspose (fun i j => A i j + F i j) = rectMatMul Q R)
    (hInv : IsInverse m R Rinv)
    (hxbar : xbar = rectTransposeMulVec (fun i j => A i j + F i j) ybar)
    (hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec
          (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec
            (fun i j => R i j + DeltaR2 i j) yhat))
    (hDeltaR1 : forall i j, |DeltaR1 i j| <= theta * |R i j|)
    (hDeltaR2 : forall i j, |DeltaR2 i j| <= theta * |R i j|)
    (hF : vecNorm2 (rectTransposeMulVec F ybar) <= EF)
    (hg : vecNorm2 g <= Eg)
    (hrem :
      vecNorm2
        (higham21SNEDHSignedRemainderAt
          F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <= ER) :
    vecNorm2 (fun j =>
        rectTransposeMulVec A yhat j + g j - xbar j) <=
      theta * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
          vecNorm2 xbar + EF + Eg + ER := by
  let B : Fin m -> Fin n -> Real := fun i j => A i j + F i j
  let lead : Fin m -> Real :=
    higham21SNEDHFactorLeadingAt R Rinv DeltaR1 DeltaR2 ybar ybar
  let first : Fin n -> Real := fun j =>
    -rectMatMulVec Q lead j - rectTransposeMulVec F ybar j + g j
  let rem : Fin n -> Real :=
    higham21SNEDHSignedRemainderAt
      F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar
  have hid := higham21_dh1993_signed_transfer_identity
    A F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar g hInv hNormal hFactor
  have hlead :
      vecNorm2 (rectMatMulVec Q lead) <=
        theta * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar := by
    simpa [B, lead] using
      higham21_dh1993_firstOrder_factor_bound
        hm theta htheta B Q R Rinv DeltaR1 DeltaR2 ybar xbar
          hQ hFactor hInv hxbar hDeltaR1 hDeltaR2
  have hfirst :
      vecNorm2 first <=
        theta * ((m : Real) + Real.sqrt (m : Real)) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar + EF + Eg := by
    have htri1 := vecNorm2_add_le
      (fun j => -rectMatMulVec Q lead j)
      (fun j => -rectTransposeMulVec F ybar j)
    have htri2 := vecNorm2_add_le
      (fun j => -rectMatMulVec Q lead j - rectTransposeMulVec F ybar j) g
    calc
      vecNorm2 first <=
          (vecNorm2 (rectMatMulVec Q lead) +
            vecNorm2 (rectTransposeMulVec F ybar)) + vecNorm2 g := by
        calc
          vecNorm2 first <=
              vecNorm2
                  (fun j => -rectMatMulVec Q lead j -
                    rectTransposeMulVec F ybar j) + vecNorm2 g := by
            simpa [first] using htri2
          _ <= (vecNorm2 (rectMatMulVec Q lead) +
                vecNorm2 (rectTransposeMulVec F ybar)) + vecNorm2 g := by
            gcongr
            simpa [vecNorm2_neg] using htri1
      _ <=
          (theta * ((m : Real) + Real.sqrt (m : Real)) *
              higham21Cond2With B (undetAplusOfGramNonsingInv B) *
              vecNorm2 xbar + EF) + Eg :=
        add_le_add (add_le_add hlead hF) hg
      _ = theta * ((m : Real) + Real.sqrt (m : Real)) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar + EF + Eg := rfl
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => first j + rem j := by
    have hx :
        (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
          fun j =>
            rectTransposeMulVec A yhat j + g j -
              rectTransposeMulVec B ybar j := by
      ext j
      rw [hxbar]
    rw [hx]
    simpa [B, first, rem, lead, higham21SNEDHSignedFirstOrderAt] using hid
  rw [herr]
  calc
    vecNorm2 (fun j => first j + rem j) <=
        vecNorm2 first + vecNorm2 rem := vecNorm2_add_le first rem
    _ <=
        (theta * ((m : Real) + Real.sqrt (m : Real)) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar + EF + Eg) + ER :=
      add_le_add hfirst (by simpa [rem] using hrem)
    _ = theta * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With (fun i j => A i j + F i j)
            (undetAplusOfGramNonsingInv (fun i j => A i j + F i j)) *
          vecNorm2 xbar + EF + Eg + ER := by rfl

/-- The exact inverse of the actual top factor, used only in the analysis. -/
noncomputable def higham21SNEHouseholderRInv
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) : Fin m -> Fin m -> Real :=
  nonsingInv m (higham21SNEHouseholderRHat fp A)

/-- Exact reference normal-equation vector for the QR-perturbed matrix. -/
noncomputable def higham21SNEHouseholderReferenceY
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin m -> Real :=
  rectMatMulVec (higham21SNEHouseholderRInv fp A)
    (rectMatMulVec (finiteTranspose (higham21SNEHouseholderRInv fp A)) b)

/-- Exact minimum-norm reference output for the QR-perturbed matrix. -/
noncomputable def higham21SNEHouseholderReferenceOutput
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    Fin (m + k) -> Real :=
  rectTransposeMulVec
    (fun i j => A i j + higham21SNEHouseholderDeltaA fp A hm hvalidQR i j)
    (higham21SNEHouseholderReferenceY fp A b)

/-- The actual rounding error committed by the final `fl(A^T y_hat)` call. -/
noncomputable def higham21SNEHouseholderFormationError
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin (m + k) -> Real :=
  let R_hat := higham21SNEHouseholderRHat fp A
  let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
  fun j =>
    higham21SNEActualOutput fp m (m + k) A R_hat b j -
      rectTransposeMulVec A y_hat j

theorem higham21_sne_householder_RHat_upper
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k))) :
    forall i j : Fin m, j.val < i.val ->
      higham21SNEHouseholderRHat fp A i j = 0 := by
  simpa [higham21SNEHouseholderRHat] using
    lsQRTallBlock_top_upper_of_upper_trapezoidal
      (higham21SNEHouseholderRTall fp A)
      (higham21_sne_householder_RTall_upper fp A hm hvalidQR)

theorem higham21_sne_householder_RHat_inverse
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    IsInverse m (higham21SNEHouseholderRHat fp A)
      (higham21SNEHouseholderRInv fp A) := by
  have hdet :
      Matrix.det
          (higham21SNEHouseholderRHat fp A : Matrix (Fin m) (Fin m) Real) ≠
        0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m
      (higham21SNEHouseholderRHat fp A)
      (higham21_sne_householder_RHat_upper fp A hm hvalidQR) hdiag
  simpa [higham21SNEHouseholderRInv] using
    isInverse_nonsingInv_of_det_ne_zero m
      (higham21SNEHouseholderRHat fp A) hdet

/-- The exact QR-perturbed reference vector solves the unrounded normal
equations with the actual top factor. -/
theorem higham21_sne_householder_referenceY_normal_eq
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    rectMatMulVec (finiteTranspose (higham21SNEHouseholderRHat fp A))
        (rectMatMulVec (higham21SNEHouseholderRHat fp A)
          (higham21SNEHouseholderReferenceY fp A b)) = b := by
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hTInv := isInverse_finiteTranspose hInv
  have hR :
      rectMatMulVec R (higham21SNEHouseholderReferenceY fp A b) =
        rectMatMulVec (finiteTranspose Rinv) b := by
    change rectMatMulVec R
        (rectMatMulVec Rinv (rectMatMulVec (finiteTranspose Rinv) b)) =
      rectMatMulVec (finiteTranspose Rinv) b
    exact rectMatMulVec_left_inverse_of_IsLeftInverse hInv.2 _
  rw [show higham21SNEHouseholderRHat fp A = R by rfl]
  rw [show higham21SNEHouseholderReferenceY fp A b =
      higham21SNEHouseholderReferenceY fp A b by rfl]
  rw [hR]
  exact rectMatMulVec_left_inverse_of_IsLeftInverse hTInv.2 b

/-- The factor-defined dual reference is exactly the canonical Gram-inverse
solution for the nearby matrix `B = A + F`. -/
theorem higham21_sne_householder_referenceY_eq_nearby_gram_inverse
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    higham21SNEHouseholderReferenceY fp A b =
      rectMatMulVec (undetGramNonsingInv B) b := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hGram : rectGram B = rectMatMul (finiteTranspose R) R :=
    higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hG : undetGramNonsingInv B =
      rectMatMul Rinv (finiteTranspose Rinv) := by
    unfold undetGramNonsingInv
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv
  calc
    higham21SNEHouseholderReferenceY fp A b =
        rectMatMulVec Rinv (rectMatMulVec (finiteTranspose Rinv) b) := by rfl
    _ = rectMatMulVec (rectMatMul Rinv (finiteTranspose Rinv)) b :=
      (rectMatMulVec_rectMatMul Rinv (finiteTranspose Rinv) b).symm
    _ = rectMatMulVec (undetGramNonsingInv B) b := by rw [hG]

/-- The exact nearby output is the canonical Gram pseudoinverse action for
`B = A + F`. -/
theorem higham21_sne_householder_referenceOutput_eq_nearby_pseudoinverse
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR =
      rectMatMulVec (undetAplusOfGramNonsingInv B) b := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  have hy := higham21_sne_householder_referenceY_eq_nearby_gram_inverse
    fp A b hm hvalidQR hdiag
  calc
    higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR =
        rectTransposeMulVec B
          (higham21SNEHouseholderReferenceY fp A b) := by rfl
    _ = rectTransposeMulVec B
          (rectMatMulVec (undetGramNonsingInv B) b) := by
      rw [show higham21SNEHouseholderReferenceY fp A b =
          rectMatMulVec (undetGramNonsingInv B) b by
        simpa [F, B] using hy]
    _ = rectMatMulVec (undetAplusOfGramNonsingInv B) b := by
      simpa [undetAplusOfGramNonsingInv] using
        (rectMatMulVec_undetAplusOfGramInv B
          (undetGramNonsingInv B) b).symm

/-- Exact source dual relation used to turn the absolute `A^T` action into
the original condition expression. -/
theorem higham21_sne_exact_dual_eq_pseudoinverse_transpose
    {m n : Nat} (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    let Aplus := undetAplusOfGramNonsingInv A
    let x := rectMatMulVec Aplus b
    let y := rectMatMulVec (undetGramNonsingInv A) b
    y = rectTransposeMulVec Aplus x := by
  dsimp only
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let y := rectMatMulVec (undetGramNonsingInv A) b
  have hRightMat : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, y, Aplus, undetAplusOfGramNonsingInv] using
      rectMatMulVec_undetAplusOfGramInv A (undetGramNonsingInv A) b
  have hleft :=
    higham21_theorem21_1_transpose_left_inverse_of_right_inverse
      A Aplus hRightMat y
  calc
    y = rectMatMulVec (finiteTranspose Aplus)
        (rectMatMulVec (finiteTranspose A) y) := hleft.symm
    _ = rectTransposeMulVec Aplus x := by
      change rectMatMulVec (finiteTranspose Aplus)
          (rectTransposeMulVec A y) =
        rectMatMulVec (finiteTranspose Aplus) x
      rw [<- hx]

/-- A fixed-radius, division-free bound for the movement of the exact dual
solution caused by the concrete Householder QR perturbation.

`beta` is any uniform Frobenius bound for the nearby Gram inverse throughout
the chosen QR radius.  The coefficient contains the fixed `radius`, not the
active QR coefficient. -/
theorem higham21_sne_householder_referenceY_source_difference_fixed_radius
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (radius beta : Real)
    (hradius : 0 <= radius) (_hbeta : 0 <= beta)
    (heta_radius :
      H19.Theorem19_4.gamma_tilde fp (m + k) m <= radius)
    (hNearbyInv :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      frobNorm (undetGramNonsingInv B) <= beta) :
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let y := rectMatMulVec (undetGramNonsingInv A) b
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let Ky :=
      frobNorm (undetGramNonsingInv A) *
        (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) * beta *
        vecNorm2 b
    vecNorm2 (fun i => ybar i - y i) <= eta * Ky := by
  dsimp only at hNearbyInv ⊢
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let GA := undetGramNonsingInv A
  let GB := undetGramNonsingInv B
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let y := rectMatMulVec GA b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let Ky := frobNorm GA *
    (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) * beta * vecNorm2 b
  have heta : 0 <= eta := by
    simpa [eta] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hAinv : IsInverse m (rectGram A) GA := by
    simpa [GA, undetGramNonsingInv] using
      isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hGram : rectGram B = rectMatMul (finiteTranspose R) R :=
    higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hGB : GB = rectMatMul Rinv (finiteTranspose Rinv) := by
    dsimp [GB, undetGramNonsingInv]
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv
  have hBright : IsRightInverse m (rectGram B) GB := by
    intro i j
    rw [hGram, hGB]
    exact IsRightInverse_rectMatMul_transpose_self_of_IsInverse hInv i j
  have hBinv : IsInverse m (rectGram B) GB :=
    ⟨isLeftInverse_of_isRightInverse (rectGram B) GB hBright, hBright⟩
  have hF : frobNorm F <= eta * frobNorm A := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_frobNorm fp A hm hvalidQR
  have hGramRaw := higham21_sne_rectGram_difference_frobNorm_le A F
  have hGramEta :
      frobNorm (fun i j => rectGram B i j - rectGram A i j) <=
        eta * (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) := by
    have hAF : 0 <= frobNorm A := frobNorm_nonneg A
    have hFF : 0 <= frobNorm F := frobNorm_nonneg F
    have hetaA : 0 <= eta * frobNorm A := mul_nonneg heta hAF
    have hlin : 2 * frobNorm A * frobNorm F <=
        2 * frobNorm A * (eta * frobNorm A) :=
      mul_le_mul_of_nonneg_left hF (mul_nonneg (by norm_num) hAF)
    have hsq : frobNorm F ^ 2 <= (eta * frobNorm A) ^ 2 :=
      (sq_le_sq₀ hFF hetaA).mpr hF
    calc
      frobNorm (fun i j => rectGram B i j - rectGram A i j) <=
          2 * frobNorm A * frobNorm F + frobNorm F ^ 2 := by
        simpa [B] using hGramRaw
      _ <= 2 * frobNorm A * (eta * frobNorm A) +
          (eta * frobNorm A) ^ 2 := add_le_add hlin hsq
      _ = eta * (2 * frobNorm A ^ 2 + eta * frobNorm A ^ 2) := by ring
      _ <= eta * (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (mul_le_mul_of_nonneg_right heta_radius (sq_nonneg _))) heta
  have hswap :
      frobNorm (fun i j => rectGram A i j - rectGram B i j) =
        frobNorm (fun i j => rectGram B i j - rectGram A i j) := by
    have hneg :
        (fun i j => rectGram A i j - rectGram B i j) =
          fun i j => -(rectGram B i j - rectGram A i j) := by
      ext i j
      ring
    rw [hneg, frobNorm_neg]
  have hInvDiff := higham21_sne_inverse_difference_frobNorm_le
    (rectGram A) (rectGram B) GA GB hAinv hBinv
  have hInvEta : frobNorm (fun i j => GB i j - GA i j) <=
      eta * (frobNorm GA *
        (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) * beta) := by
    calc
      frobNorm (fun i j => GB i j - GA i j) <=
          frobNorm GA *
            frobNorm (fun i j => rectGram A i j - rectGram B i j) *
            frobNorm GB := hInvDiff
      _ = frobNorm GA *
            frobNorm (fun i j => rectGram B i j - rectGram A i j) *
            frobNorm GB := by rw [hswap]
      _ <= frobNorm GA *
            (eta * (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2)) *
            frobNorm GB := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGramEta (frobNorm_nonneg GA))
          (frobNorm_nonneg GB)
      _ <= frobNorm GA *
            (eta * (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2)) *
            beta :=
        mul_le_mul_of_nonneg_left (by simpa [GB, B, F] using hNearbyInv)
          (mul_nonneg (frobNorm_nonneg GA)
            (mul_nonneg heta
              (add_nonneg
                (mul_nonneg (by norm_num) (sq_nonneg _))
                (mul_nonneg hradius (sq_nonneg _)))))
      _ = eta * (frobNorm GA *
          (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) * beta) := by ring
  have hybar : ybar = rectMatMulVec GB b := by
    simpa [ybar, GB, B, F] using
      higham21_sne_householder_referenceY_eq_nearby_gram_inverse
        fp A b hm hvalidQR hdiag
  have hyDiff :
      (fun i => ybar i - y i) =
        rectMatMulVec (fun i j => GB i j - GA i j) b := by
    rw [hybar]
    ext i
    dsimp [y, rectMatMulVec]
    calc
      (∑ j : Fin m, GB i j * b j) - ∑ j : Fin m, GA i j * b j =
          ∑ j : Fin m, (GB i j * b j - GA i j * b j) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin m, (GB i j - GA i j) * b j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hyDiff]
  calc
    vecNorm2 (rectMatMulVec (fun i j => GB i j - GA i j) b) <=
        frobNormRect (fun i j => GB i j - GA i j) * vecNorm2 b :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul _ _
    _ = frobNorm (fun i j => GB i j - GA i j) * vecNorm2 b := by
      rw [frobNormRect_eq_frobNorm]
    _ <= eta * (frobNorm GA *
          (2 * frobNorm A ^ 2 + radius * frobNorm A ^ 2) * beta) *
        vecNorm2 b :=
      mul_le_mul_of_nonneg_right hInvEta (vecNorm2_nonneg b)
    _ = eta * Ky := by ring

/-- Direction-radius closure for the concrete Householder perturbation.

The perturbation is normalized by its actual componentwise coefficient
`rho`; the nonnegative source envelope is the proved Householder majorant
`E = G |A|`.
The single smallness hypothesis places that concrete perturbation inside the
determinant-preserving radius from the Chapter 21 perturbation theory.  The
three conclusions are the dual displacement, primal displacement, and full
condition-times-solution transfer used below. -/
theorem higham21_sne_householder_direction_radius_transfers
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let y := rectMatMulVec G b
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kc := higham21SNEConditionTransferCoefficient
      A D b G radius beta
    vecNorm2 (fun i => ybar i - y i) <= rho * Ky /\
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx /\
      higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar <=
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
            vecNorm2 x + rho * Kc := by
  dsimp only at hrho_radius ⊢
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let y := rectMatMulVec G b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kc := higham21SNEConditionTransferCoefficient
    A D b G radius beta
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have hE : forall i j, 0 <= E i j := by
    intro i j
    dsimp [E]
    exact Finset.sum_nonneg (fun s _ =>
      mul_nonneg (higham21_sne_householder_G_nonneg hm j s) (abs_nonneg _))
  have hD : forall i j, |D i j| <= E i j := by
    intro i j
    have hFcomp :=
      higham21_sne_householder_deltaA_componentwise fp A hm hvalidQR j i
    dsimp [D]
    rw [abs_div, abs_of_pos hrho_pos]
    exact (div_le_iff₀ hrho_pos).2 (by
      calc
        |F i j| <= rho * E i j := by
          simpa [F, rho, E] using hFcomp
        _ = E i j * rho := by ring)
  have hscaled : higham21Eq21_7ScaledMatrix A D rho = B := by
    ext i j
    dsimp [higham21Eq21_7ScaledMatrix, D, B]
    rw [mul_div_cancel₀ _ (ne_of_gt hrho_pos)]
  have hyRaw :=
    higham21_sne_dual_solution_difference_vecNorm2_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  have hxRaw :=
    higham21_sne_primal_solution_difference_vecNorm2_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  have hqRaw :=
    higham21_sne_cond2_mul_solution_norm_le_direction_radius
      A D E b rho hm hdet hrho hE hD
        (by simpa [rho, D, E, F, radius] using hrho_radius)
  rw [hscaled] at hyRaw
  rw [hscaled] at hxRaw
  rw [hscaled] at hqRaw
  have hybar : ybar = rectMatMulVec (undetGramNonsingInv B) b := by
    simpa [ybar, B, F] using
      higham21_sne_householder_referenceY_eq_nearby_gram_inverse
        fp A b hm hvalidQR hdiag
  have hxbar : xbar =
      rectMatMulVec (undetAplusOfGramNonsingInv B) b := by
    simpa [xbar, B, F] using
      higham21_sne_householder_referenceOutput_eq_nearby_pseudoinverse
        fp A b hm hvalidQR hdiag
  constructor
  . change vecNorm2 (fun i => ybar i - y i) <= rho * Ky
    rw [hybar]
    simpa [G, y, Ky, radius, beta, undetGramNonsingInv,
      matMulVec, rectMatMulVec] using hyRaw
  constructor
  . change vecNorm2 (fun j => xbar j - x j) <= rho * Kx
    rw [hxbar]
    simpa [G, x, Kx, radius, beta, undetAplusOfGramNonsingInv]
      using hxRaw
  . change higham21Cond2With B (undetAplusOfGramNonsingInv B) *
        vecNorm2 xbar <=
      higham21Cond2With A (undetAplusOfGramNonsingInv A) *
        vecNorm2 x + rho * Kc
    rw [hxbar]
    simpa [G, x, Kc, radius, beta, undetAplusOfGramNonsingInv]
      using hqRaw

/-- The exact dual reference vector is the transpose of the canonical nearby
pseudoinverse applied to the nearby minimum-norm reference output. -/
theorem higham21_sne_householder_referenceY_eq_pseudoinverse_transpose
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let P := undetAplusOfGramNonsingInv B
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    ybar = rectTransposeMulVec P xbar := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let P := undetAplusOfGramNonsingInv B
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hP : P = rectMatMul Q (finiteTranspose Rinv) := by
    simpa [P] using
      higham21_sne_qr_pseudoinverse_factor B Q R Rinv hQ hFactor hInv
  have hB := higham21_sne_qr_transpose_factor B Q R hFactor
  have hTInv := isInverse_finiteTranspose hInv
  have hRight : rectMatMul B P = idMatrix m := by
    rw [hB, hP]
    calc
      rectMatMul
          (rectMatMul (finiteTranspose R) (finiteTranspose Q))
          (rectMatMul Q (finiteTranspose Rinv)) =
        rectMatMul (finiteTranspose R)
          (rectMatMul (finiteTranspose Q)
            (rectMatMul Q (finiteTranspose Rinv))) := by
              exact rectMatMul_assoc
                (finiteTranspose R) (finiteTranspose Q)
                (rectMatMul Q (finiteTranspose Rinv))
      _ = rectMatMul (finiteTranspose R)
          (rectMatMul
            (rectMatMul (finiteTranspose Q) Q)
            (finiteTranspose Rinv)) := by
              rw [<- rectMatMul_assoc
                (finiteTranspose Q) Q (finiteTranspose Rinv)]
      _ = rectMatMul (finiteTranspose R)
          (rectMatMul (idMatrix m) (finiteTranspose Rinv)) := by
            rw [hQtQ]
      _ = rectMatMul (finiteTranspose R) (finiteTranspose Rinv) := by
            rw [rectMatMul_id_left]
      _ = idMatrix m := by
        ext i j
        exact hTInv.2 i j
  have hxbar : xbar = rectTransposeMulVec B ybar := by rfl
  have hleft :=
    higham21_theorem21_1_transpose_left_inverse_of_right_inverse
      B P hRight ybar
  calc
    ybar = rectMatMulVec (finiteTranspose P)
        (rectMatMulVec (finiteTranspose B) ybar) := hleft.symm
    _ = rectTransposeMulVec P xbar := by
      change rectMatMulVec (finiteTranspose P)
          (rectTransposeMulVec B ybar) =
        rectMatMulVec (finiteTranspose P) xbar
      rw [<- hxbar]

/-- The QR perturbation action for the actual Householder panel, with no
aggregate-Gram or transferred-envelope premise.  The geometric denominator
is retained exactly, so its excess over the linear `rho` term is genuinely
higher order. -/
theorem higham21_sne_householder_qr_action_absorbed
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (rectTransposeMulVec F ybar) <=
      higham21SNEHouseholderRho fp m k /
          (1 - higham21SNEHouseholderRho fp m k) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G : Fin (m + k) -> Fin (m + k) -> Real :=
    higham21SNEHouseholderG
  let rho := higham21SNEHouseholderRho fp m k
  let P := undetAplusOfGramNonsingInv B
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  have hrho : 0 <= rho := by
    simpa [rho] using higham21_sne_householder_rho_nonneg fp hvalidQR
  have hG : forall p s, 0 <= G p s := by
    simpa [G] using (higham21_sne_householder_G_nonneg (k := k) hm)
  have hGop : rectOpNorm2Le G 1 := by
    simpa [G] using
      (higham21_sne_householder_G_rectOpNorm2Le_one (k := k) hm)
  have hF : forall p i,
      |F i p| <= rho * ∑ s : Fin (m + k), G p s * |A i s| := by
    simpa [F, G, rho] using
      higham21_sne_householder_deltaA_componentwise fp A hm hvalidQR
  have hybar : ybar = rectTransposeMulVec P xbar := by
    simpa [F, B, P, ybar, xbar] using
      higham21_sne_householder_referenceY_eq_pseudoinverse_transpose
        fp A b hm hvalidQR hdiag
  simpa [F, B, G, rho, P, ybar, xbar] using
    higham21_sne_qr_action_absorbed_by_nearby_cond2
      A F G rho hrho (by simpa [rho] using hrho_lt) hG hGop hF
      P ybar xbar hybar

/-- Source-matrix dual majorant at the exact nearby reference, specialized to
the actual Householder perturbation. -/
theorem higham21_sne_householder_source_dual_action_absorbed
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      (higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar) /
        (1 - higham21SNEHouseholderRho fp m k) := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G : Fin (m + k) -> Fin (m + k) -> Real :=
    higham21SNEHouseholderG
  let rho := higham21SNEHouseholderRho fp m k
  let P := undetAplusOfGramNonsingInv B
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  have hrho : 0 <= rho := by
    simpa [rho] using higham21_sne_householder_rho_nonneg fp hvalidQR
  have hG : forall p s, 0 <= G p s := by
    simpa [G] using (higham21_sne_householder_G_nonneg (k := k) hm)
  have hGop : rectOpNorm2Le G 1 := by
    simpa [G] using
      (higham21_sne_householder_G_rectOpNorm2Le_one (k := k) hm)
  have hF : forall p i,
      |F i p| <= rho * ∑ s : Fin (m + k), G p s * |A i s| := by
    simpa [F, G, rho] using
      higham21_sne_householder_deltaA_componentwise fp A hm hvalidQR
  have hybar : ybar = rectTransposeMulVec P xbar := by
    simpa [F, B, P, ybar, xbar] using
      higham21_sne_householder_referenceY_eq_pseudoinverse_transpose
        fp A b hm hvalidQR hdiag
  simpa [F, B, G, rho, P, ybar, xbar] using
    higham21_sne_source_dual_action_absorbed_by_nearby_cond2
      A F G rho hrho (by simpa [rho] using hrho_lt) hG hGop hF
      P ybar xbar hybar

/-- Componentwise error of the actual final rounded transpose action. -/
theorem higham21_sne_householder_formation_error_pointwise
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hmGamma : gammaValid fp m) :
    let R_hat := higham21SNEHouseholderRHat fp A
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    forall j,
      |higham21SNEHouseholderFormationError fp A b j| <=
        gamma fp m *
          rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|) j := by
  dsimp only
  intro j
  simpa [higham21SNEHouseholderFormationError,
    higham21SNEActualOutput, rectTransposeMulVec, finiteTranspose,
    absMatrixRect] using
      (matVec_error_bound fp (m + k) m (finiteTranspose A)
        (higham21SNEComputedNormalSolution fp m
          (higham21SNEHouseholderRHat fp A) b) hmGamma j)

/-- Normwise consequence of the preceding componentwise final-formation
bound. -/
theorem higham21_sne_householder_formation_error_norm
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hmGamma : gammaValid fp m) :
    let R_hat := higham21SNEHouseholderRHat fp A
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    vecNorm2 (higham21SNEHouseholderFormationError fp A b) <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) := by
  dsimp only
  let w : Fin (m + k) -> Real :=
    rectTransposeMulVec (absMatrixRect A)
      (fun i =>
        |higham21SNEComputedNormalSolution fp m
          (higham21SNEHouseholderRHat fp A) b i|)
  have hpoint : forall j,
      |higham21SNEHouseholderFormationError fp A b j| <=
        gamma fp m * w j := by
    simpa [w] using
      higham21_sne_householder_formation_error_pointwise
        fp A b hmGamma
  calc
    vecNorm2 (higham21SNEHouseholderFormationError fp A b) <=
        vecNorm2 (fun j => gamma fp m * w j) :=
      vecNorm2_le_of_abs_le _ _ hpoint
    _ = gamma fp m * vecNorm2 w := by
      rw [vecNorm2_smul, abs_of_nonneg (gamma_nonneg fp hmGamma)]
    _ = gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A)
            (fun i =>
              |higham21SNEComputedNormalSolution fp m
                (higham21SNEHouseholderRHat fp A) b i|)) := by rfl

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11), SNE
Householder path up to the QR-perturbed exact reference.

The theorem instantiates the actual panel top block, both rounded triangular
solves, and the final rounded `A^T` product.  Its three quantitative premises
are local: the QR perturbation acting on the exact dual vector, a majorant for
the final matrix-vector call, and the explicit signed higher-order expression.
None of them assumes the displayed output-error conclusion. -/
theorem higham21_sne_householder_actual_output_signed_reference_bound
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (cF cg C : Real)
    (hQRAction :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2 (rectTransposeMulVec F ybar) <=
        gamma fp m * cF *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hFormationMajorant :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let R_hat := higham21SNEHouseholderRHat fp A
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) <=
        cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hSignedRemainder :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let Q := higham21SNEHouseholderEconomyQ fp A
      let R := higham21SNEHouseholderRHat fp A
      let Rinv := higham21SNEHouseholderRInv fp A
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let yhat := higham21SNEComputedNormalSolution fp m R b
      forall DeltaR1 DeltaR2 : Fin m -> Fin m -> Real,
        (forall i j, |DeltaR1 i j| <= gamma fp m * |R i j|) ->
        (forall i j, |DeltaR2 i j| <= gamma fp m * |R i j|) ->
        (forall i,
          (∑ r : Fin m, (R r i + DeltaR1 r i) *
            (∑ j : Fin m, (R r j + DeltaR2 r j) * yhat j)) = b i) ->
        vecNorm2
          (higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
          gamma fp m ^ 2 * C) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let R_hat := higham21SNEHouseholderRHat fp A
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => x_hat j - xbar j) <=
      gamma fp m *
          ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by
  dsimp only at hQRAction hFormationMajorant hSignedRemainder ⊢
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let g := higham21SNEHouseholderFormationError fp A b
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using
      higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hxbar : xbar = rectTransposeMulVec B ybar := by
    rfl
  have hg0 : vecNorm2 g <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := by
    simpa [g, R, yhat] using
      higham21_sne_householder_formation_error_norm fp A b hmGamma
  have hg : vecNorm2 g <=
      gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
        vecNorm2 xbar := by
    calc
      vecNorm2 g <= gamma fp m *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := hg0
      _ <= gamma fp m *
          (cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar) :=
        mul_le_mul_of_nonneg_left (by simpa [B, F, R, yhat, xbar] using
          hFormationMajorant) (gamma_nonneg fp hmGamma)
      _ = gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring
  have hrem := hSignedRemainder DeltaR1 DeltaR2
    (by simpa [R] using hDeltaR1) (by simpa [R] using hDeltaR2)
    (by simpa [R, yhat] using hsolve)
  have hCore := higham21_dh1993_signed_output_bound
    hm (gamma fp m) cF cg C (gamma_nonneg fp hmGamma)
      A F Q R Rinv DeltaR1 DeltaR2 ybar yhat xbar g
      hQ hFactor hInv hxbar hNormal hDeltaR1 hDeltaR2
      (by simpa [F, B, ybar, xbar] using hQRAction) hg
      (by simpa [F, Q, R, Rinv, ybar, yhat] using hrem)
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => higham21SNEActualOutput fp m (m + k) A R b j - xbar j := by
    ext j
    simp [g, higham21SNEHouseholderFormationError, R, yhat]
  rw [herr] at hCore
  simpa [F, B, R, xbar] using hCore

/-- Concrete signed Householder-SNE bound with the QR-action premise closed
from the actual panel's componentwise Higham certificate.

Unlike the compatibility wrapper above, the coefficient keeps the exact
`rho / (1-rho)` term.  Thus it is valid at finite roundoff and separates into
the linear `rho` contribution plus a genuine quadratic geometric remainder. -/
theorem higham21_sne_householder_actual_output_signed_reference_bound_closed_qr
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (cg C : Real)
    (hFormationMajorant :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let R_hat := higham21SNEHouseholderRHat fp A
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) <=
        cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hSignedRemainder :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let Q := higham21SNEHouseholderEconomyQ fp A
      let R := higham21SNEHouseholderRHat fp A
      let Rinv := higham21SNEHouseholderRInv fp A
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let yhat := higham21SNEComputedNormalSolution fp m R b
      forall DeltaR1 DeltaR2 : Fin m -> Fin m -> Real,
        (forall i j, |DeltaR1 i j| <= gamma fp m * |R i j|) ->
        (forall i j, |DeltaR2 i j| <= gamma fp m * |R i j|) ->
        (forall i,
          (∑ r : Fin m, (R r i + DeltaR1 r i) *
            (∑ j : Fin m, (R r j + DeltaR2 r j) * yhat j)) = b i) ->
        vecNorm2
          (higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
          gamma fp m ^ 2 * C) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let R_hat := higham21SNEHouseholderRHat fp A
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => x_hat j - xbar j) <=
      (gamma fp m * ((m : Real) + Real.sqrt (m : Real)) +
          rho / (1 - rho) + gamma fp m * cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by
  dsimp only at hFormationMajorant hSignedRemainder ⊢
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let g := higham21SNEHouseholderFormationError fp A b
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using
      higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hxbar : xbar = rectTransposeMulVec B ybar := by rfl
  have hqr : vecNorm2 (rectTransposeMulVec F ybar) <=
      rho / (1 - rho) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
    simpa [rho, F, B, ybar, xbar] using
      higham21_sne_householder_qr_action_absorbed
        fp A b hm hvalidQR hdiag hrho_lt
  have hg0 : vecNorm2 g <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := by
    simpa [g, R, yhat] using
      higham21_sne_householder_formation_error_norm fp A b hmGamma
  have hg : vecNorm2 g <=
      gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
    calc
      vecNorm2 g <= gamma fp m *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := hg0
      _ <= gamma fp m *
          (cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar) :=
        mul_le_mul_of_nonneg_left (by simpa [B, F, R, yhat, xbar] using
          hFormationMajorant) (gamma_nonneg fp hmGamma)
      _ = gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring
  have hrem := hSignedRemainder DeltaR1 DeltaR2
    (by simpa [R] using hDeltaR1) (by simpa [R] using hDeltaR2)
    (by simpa [R, yhat] using hsolve)
  have hCore := higham21_dh1993_signed_output_bound_separate
    hm (gamma fp m)
      (rho / (1 - rho) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
      (gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
      (gamma fp m ^ 2 * C)
      (gamma_nonneg fp hmGamma)
      A F Q R Rinv DeltaR1 DeltaR2 ybar yhat xbar g
      hQ hFactor hInv hxbar hNormal hDeltaR1 hDeltaR2 hqr hg
      (by simpa [F, Q, R, Rinv, ybar, yhat] using hrem)
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => higham21SNEActualOutput fp m (m + k) A R b j - xbar j := by
    ext j
    simp [g, higham21SNEHouseholderFormationError, R, yhat]
  rw [herr] at hCore
  calc
    vecNorm2 (fun j =>
        higham21SNEActualOutput fp m (m + k) A R b j - xbar j) <=
      gamma fp m * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        rho / (1 - rho) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        gamma fp m ^ 2 * C := hCore
    _ = (gamma fp m * ((m : Real) + Real.sqrt (m : Real)) +
          rho / (1 - rho) + gamma fp m * cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by ring

/-- Fully closed finite-roundoff bound for the actual Householder-SNE output
relative to its exact QR-perturbed reference.

Both rounded triangular solves and the final rounded transpose product are
the computed quantities.  All higher-order products are bounded explicitly
by the square of the master radius `theta = gamma_m + rho_QR`; there is no
QR-action, formation-majorant, signed-remainder, or transferred-envelope
premise. -/
theorem higham21_sne_householder_actual_output_uniform_quadratic_bound
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let q := higham21Cond2With B (undetAplusOfGramNonsingInv B) *
      vecNorm2 xbar
    let Kd :=
      frobNorm Rinv *
        (frobNorm R +
          frobNorm Rinv * frobNorm R *
            (frobNorm R + theta * frobNorm R)) *
        vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 *
          (2 * (q / (1 - rho)) + frobNorm A * Kd + Crem) := by
  dsimp only
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let q := higham21Cond2With B (undetAplusOfGramNonsingInv B) *
    vecNorm2 xbar
  let Kd :=
    frobNorm Rinv *
      (frobNorm R +
        frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) *
      vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let g := higham21SNEHouseholderFormationError fp A b
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have heta : 0 <= eta := by
    simpa [eta] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := by
    simpa [rho] using higham21_sne_householder_rho_nonneg fp hvalidQR
  have htheta : 0 <= theta := by
    simpa [theta] using add_nonneg hgamma hrho
  have hgamma_theta : gammaM <= theta := by
    dsimp [theta]
    linarith
  have hrho_theta : rho <= theta := by
    dsimp [theta]
    linarith
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  have hn_one_nat : 1 <= m + k := Nat.succ_le_iff.mpr hn
  have hn_one_real : (1 : Real) <= (m + k : Real) := by
    exact_mod_cast hn_one_nat
  have heta_rho : eta <= rho := by
    calc
      eta = (1 : Real) * eta := by ring
      _ <= (m + k : Real) * eta :=
        mul_le_mul_of_nonneg_right hn_one_real heta
      _ = rho := by
        simp [rho, eta, higham21SNEHouseholderRho]
  have heta_theta : eta <= theta := heta_rho.trans hrho_theta
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using
      higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hDeltaR1theta : forall i j,
      |DeltaR1 i j| <= theta * |R i j| := by
    intro i j
    exact (hDeltaR1 i j).trans
      (mul_le_mul_of_nonneg_right hgamma_theta (abs_nonneg _))
  have hDeltaR2theta : forall i j,
      |DeltaR2 i j| <= theta * |R i j| := by
    intro i j
    exact (hDeltaR2 i j).trans
      (mul_le_mul_of_nonneg_right hgamma_theta (abs_nonneg _))
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hxbar : xbar = rectTransposeMulVec B ybar := by rfl
  have hq : 0 <= q := by
    exact mul_nonneg
      (higham21Cond2With_nonneg B (undetAplusOfGramNonsingInv B))
      (vecNorm2_nonneg xbar)
  have hKd : 0 <= Kd := by
    dsimp [Kd]
    exact mul_nonneg
      (mul_nonneg (frobNorm_nonneg Rinv)
        (add_nonneg (frobNorm_nonneg R)
          (mul_nonneg
            (mul_nonneg (frobNorm_nonneg Rinv) (frobNorm_nonneg R))
            (add_nonneg (frobNorm_nonneg R)
              (mul_nonneg htheta (frobNorm_nonneg R))))))
      (vecNorm2_nonneg yhat)
  have hFbase : frobNorm F <= eta * frobNorm A := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_frobNorm fp A hm hvalidQR
  have hFtheta : frobNorm F <= theta * frobNorm A := by
    exact hFbase.trans
      (mul_le_mul_of_nonneg_right heta_theta (frobNorm_nonneg A))
  have hdiff : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd := by
    simpa [Kd] using
      higham21_dh1993_factor_difference_vecNorm2_le_radius
        theta theta htheta le_rfl R Rinv DeltaR1 DeltaR2 ybar yhat
          hInv hNormal hDeltaR1theta hDeltaR2theta
  have hsource :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
        q / (1 - rho) := by
    simpa [F, B, ybar, xbar, q, rho] using
      higham21_sne_householder_source_dual_action_absorbed
        fp A b hm hvalidQR hdiag hrho_lt
  have hg0 : vecNorm2 g <=
      gammaM *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := by
    simpa [g, gammaM, R, yhat] using
      higham21_sne_householder_formation_error_norm fp A b hmGamma
  have hg : vecNorm2 g <=
      gammaM * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
    exact higham21_sne_formation_error_le_gamma_plus_uniform_quadratic
      theta rho gammaM Kd q htheta hrho hrho_theta
        (by simpa [rho] using hrho_lt) hgamma hgamma_theta hKd hq
        A ybar yhat g hg0 hsource hdiff
  have hqr : vecNorm2 (rectTransposeMulVec F ybar) <=
      rho / (1 - rho) * q := by
    calc
      vecNorm2 (rectTransposeMulVec F ybar) <=
          rho / (1 - rho) *
            higham21Cond2With B (undetAplusOfGramNonsingInv B) *
              vecNorm2 xbar := by
        simpa [rho, F, B, ybar, xbar] using
          higham21_sne_householder_qr_action_absorbed
            fp A b hm hvalidQR hdiag hrho_lt
      _ = rho / (1 - rho) * q := by
        simp [q]
        ring
  have hrem :
      vecNorm2
          (higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
        theta ^ 2 * Crem := by
    simpa [Kd, Crem] using
      higham21_dh1993_signed_remainder_vecNorm2_le_radius
        theta theta (frobNorm A) htheta le_rfl (frobNorm_nonneg A)
          F Q R Rinv DeltaR1 DeltaR2 ybar yhat hQ hInv hNormal
          hDeltaR1theta hDeltaR2theta hFtheta
  have hCore := higham21_dh1993_signed_output_bound_separate
    hm gammaM
      (rho / (1 - rho) * q)
      (gammaM * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd))
      (theta ^ 2 * Crem) hgamma
      A F Q R Rinv DeltaR1 DeltaR2 ybar yhat xbar g
      hQ hFactor hInv hxbar hNormal
      (by simpa [gammaM] using hDeltaR1)
      (by simpa [gammaM] using hDeltaR2)
      hqr hg hrem
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => higham21SNEActualOutput fp m (m + k) A R b j - xbar j := by
    ext j
    simp [g, higham21SNEHouseholderFormationError, R, yhat]
  rw [herr] at hCore
  have hCore' :
      vecNorm2 (fun j =>
          higham21SNEActualOutput fp m (m + k) A R b j - xbar j) <=
        gammaM * ((m : Real) + Real.sqrt (m : Real)) * q +
          rho / (1 - rho) * q +
          (gammaM * q +
            theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd)) +
          theta ^ 2 * Crem := by
    calc
      vecNorm2 (fun j =>
          higham21SNEActualOutput fp m (m + k) A R b j - xbar j) <=
        gammaM * ((m : Real) + Real.sqrt (m : Real)) *
              higham21Cond2With B (undetAplusOfGramNonsingInv B) *
              vecNorm2 xbar +
            rho / (1 - rho) * q +
            (gammaM * q +
              theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd)) +
            theta ^ 2 * Crem := hCore
      _ = gammaM * ((m : Real) + Real.sqrt (m : Real)) * q +
          rho / (1 - rho) * q +
          (gammaM * q +
            theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd)) +
          theta ^ 2 * Crem := by
        simp [q]
        ring
  have hden : 0 < 1 - rho := sub_pos.mpr (by simpa [rho] using hrho_lt)
  have hqdiv : 0 <= q / (1 - rho) := div_nonneg hq hden.le
  have hrhoSq : rho ^ 2 <= theta ^ 2 := by
    nlinarith
  have hidentity : q / (1 - rho) = q + rho * (q / (1 - rho)) := by
    field_simp [ne_of_gt hden]
    ring
  have hqrSplit : rho / (1 - rho) * q <=
      rho * q + theta ^ 2 * (q / (1 - rho)) := by
    calc
      rho / (1 - rho) * q = rho * (q / (1 - rho)) := by ring
      _ = rho * (q + rho * (q / (1 - rho))) :=
        congrArg (fun z => rho * z) hidentity
      _ = rho * q + rho ^ 2 * (q / (1 - rho)) := by ring
      _ <= rho * q + theta ^ 2 * (q / (1 - rho)) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hrhoSq hqdiv)
  calc
    vecNorm2 (fun j =>
        higham21SNEActualOutput fp m (m + k) A R b j - xbar j) <=
      gammaM * ((m : Real) + Real.sqrt (m : Real)) * q +
        rho / (1 - rho) * q +
        (gammaM * q +
          theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd)) +
        theta ^ 2 * Crem := hCore'
    _ <= gammaM * ((m : Real) + Real.sqrt (m : Real)) * q +
        (rho * q + theta ^ 2 * (q / (1 - rho))) +
        (gammaM * q +
          theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd)) +
        theta ^ 2 * Crem := by
      gcongr
    _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 *
          (2 * (q / (1 - rho)) + frobNorm A * Kd + Crem) := by ring

/-- Source-facing form of the fully closed actual-to-reference estimate.

The first-order condition expression is now the original
`cond2(A) * ||A^+ b||`.  The displayed square coefficient is a concrete
finite-roundoff coefficient: it may contain the active nearby quantity
`qB / (1-rho)` and the actual rounded normal solution, but it contains no
assumed error bound, no quotient by the master radius, and no quantity chosen
from the conclusion. -/
theorem higham21_sne_householder_actual_output_source_finite_quadratic_bound
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R +
          frobNorm Rinv * frobNorm R *
            (frobNorm R + theta * frobNorm R)) *
        vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 * Cfinite := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R +
        frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) *
      vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let s := (m : Real) + Real.sqrt (m : Real)
  let L := gammaM * s + rho + gammaM
  have hgamma : 0 <= gammaM := by
    simpa [gammaM] using gamma_nonneg fp hmGamma
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have htheta : 0 <= theta := add_nonneg hgamma hrho
  have hrho_theta : rho <= theta := by dsimp [theta]; linarith
  have hs : 0 <= s := by
    exact add_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg _)
  have hradius : 0 <= radius := by
    exact hrho.trans (by simpa [rho, F, D, E, radius] using hrho_radius)
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21PerturbationGramInverseBound_nonneg A
  have hKc : 0 <= Kc := by
    simpa [Kc] using
      higham21_sne_conditionTransferCoefficient_nonneg
        A D b G radius beta hradius hbeta
  have hqTransfer : qB <= q + rho * Kc := by
    simpa [rho, F, D, E, B, G, radius, beta, x, xbar, q, qB, Kc] using
      (higham21_sne_householder_direction_radius_transfers
        fp A b hm hvalidQR hdiag hdet hrho_pos hrho_radius).2.2
  have hCore : vecNorm2 (fun j => xhat j - xbar j) <=
      L * qB + theta ^ 2 *
        (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) := by
    simpa [gammaM, rho, theta, F, B, R, Rinv, yhat, xhat, xbar,
      qB, Kd, Crem, s, L] using
      higham21_sne_householder_actual_output_uniform_quadratic_bound
        fp A b hm hvalidQR hmGamma hdiag hrho_lt
  have hL : 0 <= L := by
    dsimp [L]
    exact add_nonneg (add_nonneg (mul_nonneg hgamma hs) hrho) hgamma
  have hLtheta : L <= theta * (s + 2) := by
    dsimp [L, theta]
    nlinarith [mul_nonneg hrho hs]
  have hLrho : L * rho <= theta ^ 2 * (s + 2) := by
    calc
      L * rho <= (theta * (s + 2)) * rho :=
        mul_le_mul_of_nonneg_right hLtheta hrho
      _ <= (theta * (s + 2)) * theta :=
        mul_le_mul_of_nonneg_left hrho_theta
          (mul_nonneg htheta (by linarith))
      _ = theta ^ 2 * (s + 2) := by ring
  have hlead : L * qB <= L * q + theta ^ 2 * ((s + 2) * Kc) := by
    calc
      L * qB <= L * (q + rho * Kc) :=
        mul_le_mul_of_nonneg_left hqTransfer hL
      _ = L * q + (L * rho) * Kc := by ring
      _ <= L * q + (theta ^ 2 * (s + 2)) * Kc :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hLrho hKc)
      _ = L * q + theta ^ 2 * ((s + 2) * Kc) := by ring
  calc
    vecNorm2 (fun j => xhat j - xbar j) <=
        L * qB + theta ^ 2 *
          (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) := hCore
    _ <= (L * q + theta ^ 2 * ((s + 2) * Kc)) +
        theta ^ 2 *
          (2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem) :=
      add_le_add hlead le_rfl
    _ = L * q + theta ^ 2 * Cfinite := by
      simp [Cfinite]
      ring

/-- The QR-perturbed reference output is feasible for the perturbed system and
has the economy-factor transpose representation used by the signed proof. -/
theorem higham21_sne_householder_reference_system
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let ybar := higham21SNEHouseholderReferenceY fp A b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    rectMatMulVec B xbar = b /\ xbar = rectTransposeMulVec B ybar := by
  dsimp only
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hGram : rectGram B = rectMatMul (finiteTranspose R) R :=
    higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  have hxbar : xbar = rectTransposeMulVec B ybar := by rfl
  refine ⟨?_, hxbar⟩
  change rectMatMulVec B xbar = b
  rw [hxbar, rectMatMulVec_rectTransposeMulVec]
  change rectMatMulVec (rectGram B) ybar = b
  rw [hGram]
  rw [rectMatMulVec_rectMatMul]
  exact hbar

/-- The exact QR-reference displacement is controlled by the already-proved
equation-(21.11) rowwise first-order theorem, plus its explicit finite
remainder.  This is the QR-reference edge needed before combining the signed
SNE error with the exact solution for `A`. -/
theorem higham21_sne_householder_reference_forward_error
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (CQR : Real)
    (hQRRemainder :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2
          (higham21Eq21_11FiniteRemainder A F b xbar ybar) <=
        H19.Theorem19_4.gamma_tilde fp (m + k) m ^ 2 * CQR) :
    let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => xbar j - x j) <=
      (m + k : Real) * etaQR *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x +
        etaQR ^ 2 * CQR := by
  dsimp only at hQRRemainder ⊢
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  have hsystem :=
    (higham21_sne_householder_reference_system
      fp A b hm hvalidQR hdiag).1
  have hrange :=
    (higham21_sne_householder_reference_system
      fp A b hm hvalidQR hdiag).2
  have hexpand := higham21_eq21_11_exact_finite_forward_expansion
    A F b xbar ybar hdet (by simpa [B, F, xbar] using hsystem)
      (by simpa [B, F, ybar, xbar] using hrange)
  have heta : 0 <= etaQR := by
    simpa [etaQR] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hfirst := higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
    A F b hn hdet heta
      (by simpa [F, etaQR] using
        higham21_sne_householder_deltaA_rowwise fp A hm hvalidQR)
  rw [hexpand]
  calc
    vecNorm2
        (fun j =>
          higham21Eq21_11FirstOrder A F b j +
            higham21Eq21_11FiniteRemainder A F b xbar ybar j) <=
      vecNorm2 (higham21Eq21_11FirstOrder A F b) +
        vecNorm2 (higham21Eq21_11FiniteRemainder A F b xbar ybar) :=
      vecNorm2_add_le _ _
    _ <=
        ((m + k : Real) * etaQR *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) *
            vecNorm2 x) + etaQR ^ 2 * CQR :=
      add_le_add (by simpa [etaQR, F, x] using hfirst)
        (by simpa [etaQR, F, ybar, xbar] using hQRRemainder)
    _ = (m + k : Real) * etaQR *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + etaQR ^ 2 * CQR := rfl

/-- Equation (21.11) for the exact QR reference with its finite remainder
closed from the concrete direction-radius transfer.

Unlike the compatibility theorem above, this result has no supplied
remainder premise. -/
theorem higham21_sne_householder_reference_forward_error_closed_direction_radius
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xbar j - x j) <=
      rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR := by
  dsimp only at hrho_radius ⊢
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let y := rectMatMulVec G b
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let CQR := frobNorm A *
    ((1 + frobNorm Aplus * frobNorm A) * KyEta +
      frobNorm Aplus * KxEta)
  have heta : 0 <= eta := by
    simpa [eta] using H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hrho : 0 <= rho := by simpa [rho] using hrho_pos.le
  have hradius : 0 <= radius := by
    exact hrho.trans (by simpa [rho, F, D, E, radius] using hrho_radius)
  have hbeta : 0 <= beta := by
    simpa [beta] using higham21PerturbationGramInverseBound_nonneg A
  have hKy : 0 <= Ky := by
    dsimp [Ky]
    exact mul_nonneg
      (higham21_sne_inverseDifferenceCoefficient_nonneg
        A D G radius beta hradius hbeta)
      (vecNorm2_nonneg b)
  have hKx : 0 <= Kx := by
    dsimp [Kx]
    exact mul_nonneg
      (higham21_sne_pseudoinverseDifferenceCoefficient_nonneg
        A D G radius beta hradius hbeta)
      (vecNorm2_nonneg b)
  have hnreal : 0 <= (m + k : Real) := by positivity
  have hKyEta : 0 <= KyEta := mul_nonneg hnreal hKy
  have hKxEta : 0 <= KxEta := mul_nonneg hnreal hKx
  have hrho_eta : rho = (m + k : Real) * eta := by
    simp [rho, eta, higham21SNEHouseholderRho]
  have htrans := higham21_sne_householder_direction_radius_transfers
    fp A b hm hvalidQR hdiag hdet hrho_pos hrho_radius
  have hyRho : vecNorm2 (fun i => ybar i - y i) <= rho * Ky := by
    simpa [rho, F, D, E, G, radius, beta, y, ybar, Ky] using htrans.1
  have hxRho : vecNorm2 (fun j => xbar j - x j) <= rho * Kx := by
    simpa [rho, F, D, E, G, radius, beta, x, xbar, Kx, Aplus] using
      htrans.2.1
  have hyEta : vecNorm2 (fun i => ybar i - y i) <= eta * KyEta := by
    calc
      vecNorm2 (fun i => ybar i - y i) <= rho * Ky := hyRho
      _ = eta * KyEta := by rw [hrho_eta]; simp [KyEta]; ring
  have hxEta : vecNorm2 (fun j => xbar j - x j) <= eta * KxEta := by
    calc
      vecNorm2 (fun j => xbar j - x j) <= rho * Kx := hxRho
      _ = eta * KxEta := by rw [hrho_eta]; simp [KxEta]; ring
  have hyExact : y = rectTransposeMulVec Aplus x := by
    simpa [y, Aplus, x, G] using
      higham21_sne_exact_dual_eq_pseudoinverse_transpose A b hdet
  have hF : frobNorm F <= eta * frobNorm A := by
    simpa [F, eta] using
      higham21_sne_householder_deltaA_frobNorm fp A hm hvalidQR
  have hrem : vecNorm2
      (higham21Eq21_11FiniteRemainder A F b xbar ybar) <=
        eta ^ 2 * CQR := by
    have hfinite := higham21_eq21_11_finite_remainder_vecNorm2_le_radius
      eta (frobNorm A) KyEta KxEta heta (frobNorm_nonneg A)
        hKyEta hKxEta A F b xbar ybar hF
        (by
          dsimp only
          rw [← hyExact]
          exact hyEta)
        (by simpa [Aplus, x] using hxEta)
    simpa [CQR, Aplus] using hfinite
  have href := higham21_sne_householder_reference_forward_error
    fp A b hm hn hvalidQR hdiag hdet CQR
      (by simpa [F, eta, ybar, xbar] using hrem)
  calc
    vecNorm2 (fun j => xbar j - x j) <=
        (m + k : Real) * eta *
            higham21Cond2With A Aplus * vecNorm2 x + eta ^ 2 * CQR := by
      simpa [eta, x, xbar, Aplus] using href
    _ = rho * higham21Cond2With A Aplus * vecNorm2 x +
        eta ^ 2 * CQR := by rw [hrho_eta]

/-- Fully assembled finite-roundoff forward bound for the actual Householder
SNE output and the canonical exact solution of the original system.

Every algorithmic error certificate (QR, both triangular solves, final
formation, condition transfer, and the finite equation-(21.11) remainder) is
instantiated internally. -/
theorem higham21_sne_householder_actual_output_source_forward_finite_bound
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xhat j - x j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * q +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let q := higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let CQR := frobNorm A *
    ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
      frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
  have hactual : vecNorm2 (fun j => xhat j - xbar j) <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
        theta ^ 2 * Cfinite := by
    simpa [gammaM, rho, theta, F, D, E, B, G, radius, beta, R, Rinv,
      yhat, xhat, x, xbar, q, qB, Kc, Kd, Crem, Cfinite] using
      higham21_sne_householder_actual_output_source_finite_quadratic_bound
        fp A b hm hvalidQR hmGamma hdiag hdet hrho_pos hrho_lt hrho_radius
  have href : vecNorm2 (fun j => xbar j - x j) <=
      rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR := by
    simpa [eta, rho, F, D, E, G, radius, beta, x, xbar, Ky, Kx,
      KyEta, KxEta, CQR] using
      higham21_sne_householder_reference_forward_error_closed_direction_radius
        fp A b hm hn hvalidQR hdiag hdet hrho_pos hrho_radius
  have hsplit : (fun j => xhat j - x j) =
      fun j => (xhat j - xbar j) + (xbar j - x j) := by
    ext j
    ring
  rw [hsplit]
  calc
    vecNorm2 (fun j => (xhat j - xbar j) + (xbar j - x j)) <=
        vecNorm2 (fun j => xhat j - xbar j) +
          vecNorm2 (fun j => xbar j - x j) := vecNorm2_add_le _ _
    _ <= ((gammaM * ((m : Real) + Real.sqrt (m : Real)) + rho + gammaM) * q +
          theta ^ 2 * Cfinite) +
        (rho * higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2 x + eta ^ 2 * CQR) := add_le_add hactual href
    _ = (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) * q +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
      simp [q]
      ring

/-- Higham, 2nd ed., Chapter 21, equation (21.11): source-active relative
forward endpoint for the actual Householder seminormal-equations algorithm.

The right-hand side is nonzero, so the exact minimum-norm solution provides a
valid relative normalization.  The first-order term is entirely in the
original source condition number.  The remaining displayed quotient is an
explicit finite second-order coefficient built from the active QR direction,
the actual rounded normal solution, and fixed-radius perturbation data; it is
not a supplied error certificate. -/
theorem higham21_sne_householder_actual_output_source_forward_relative_finite
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m) (hn : 2 <= m + k)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hrho_pos : 0 < higham21SNEHouseholderRho fp m k)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (hrho_radius :
      let rho := higham21SNEHouseholderRho fp m k
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
      let E : Fin m -> Fin (m + k) -> Real := fun i p =>
        ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
      rho <= higham21PerturbationDirectionRadius A D E) :
    let gammaM := gamma fp m
    let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let rho := higham21SNEHouseholderRho fp m k
    let theta := gammaM + rho
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
    let E : Fin m -> Fin (m + k) -> Real := fun i p =>
      ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let G := undetGramNonsingInv A
    let radius := higham21PerturbationDirectionRadius A D E
    let beta := higham21PerturbationGramInverseBound A
    let R := higham21SNEHouseholderRHat fp A
    let Rinv := higham21SNEHouseholderRInv fp A
    let yhat := higham21SNEComputedNormalSolution fp m R b
    let xhat := higham21SNEActualOutput fp m (m + k) A R b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
    let Ky := higham21Eq21_7InverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let Kx := higham21SNEPseudoinverseDifferenceCoefficient
      A D G radius beta * vecNorm2 b
    let KyEta := (m + k : Real) * Ky
    let KxEta := (m + k : Real) * Kx
    let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
    let Kd :=
      frobNorm Rinv *
        (frobNorm R + frobNorm Rinv * frobNorm R *
          (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
    let Crem :=
      frobNorm R * Kd +
        frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
        frobNorm A * Kd
    let Cfinite :=
      ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
        2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
    let CQR := frobNorm A *
      ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * KyEta +
        frobNorm (undetAplusOfGramNonsingInv A) * KxEta)
    vecNorm2 (fun j => xhat j - x j) / vecNorm2 x <=
      (gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) +
        (theta ^ 2 * Cfinite + eta ^ 2 * CQR) / vecNorm2 x := by
  dsimp only at hrho_radius ⊢
  let gammaM := gamma fp m
  let eta := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let rho := higham21SNEHouseholderRho fp m k
  let theta := gammaM + rho
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let D : Fin m -> Fin (m + k) -> Real := fun i j => F i j / rho
  let E : Fin m -> Fin (m + k) -> Real := fun i p =>
    ∑ s : Fin (m + k), higham21SNEHouseholderG p s * |A i s|
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let G := undetGramNonsingInv A
  let radius := higham21PerturbationDirectionRadius A D E
  let beta := higham21PerturbationGramInverseBound A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xhat := higham21SNEActualOutput fp m (m + k) A R b
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let qB := higham21Cond2With B (undetAplusOfGramNonsingInv B) * vecNorm2 xbar
  let Ky := higham21Eq21_7InverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let Kx := higham21SNEPseudoinverseDifferenceCoefficient
    A D G radius beta * vecNorm2 b
  let KyEta := (m + k : Real) * Ky
  let KxEta := (m + k : Real) * Kx
  let Kc := higham21SNEConditionTransferCoefficient A D b G radius beta
  let Kd :=
    frobNorm Rinv *
      (frobNorm R + frobNorm Rinv * frobNorm R *
        (frobNorm R + theta * frobNorm R)) * vecNorm2 yhat
  let Crem :=
    frobNorm R * Kd +
      frobNorm Rinv * frobNorm R ^ 2 * (vecNorm2 yhat + Kd) +
      frobNorm A * Kd
  let Cfinite :=
    ((m : Real) + Real.sqrt (m : Real) + 2) * Kc +
      2 * (qB / (1 - rho)) + frobNorm A * Kd + Crem
  let CQR := frobNorm A *
    ((1 + frobNorm Aplus * frobNorm A) * KyEta + frobNorm Aplus * KxEta)
  let lead := gammaM * ((m : Real) + Real.sqrt (m : Real)) + 2 * rho + gammaM
  have hbound : vecNorm2 (fun j => xhat j - x j) <=
      lead * (higham21Cond2With A Aplus * vecNorm2 x) +
        theta ^ 2 * Cfinite + eta ^ 2 * CQR := by
    simpa [gammaM, eta, rho, theta, F, D, E, B, G, radius, beta,
      R, Rinv, yhat, xhat, x, xbar, qB, Ky, Kx, KyEta, KxEta,
      Kc, Kd, Crem, Cfinite, CQR, lead, Aplus] using
      higham21_sne_householder_actual_output_source_forward_finite_bound
        fp A b hm hn hvalidQR hmGamma hdiag hdet hrho_pos hrho_lt hrho_radius
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
  have hxne : x ≠ 0 := by
    intro hx0
    apply hb
    calc
      b = rectMatMulVec A x := hAx.symm
      _ = 0 := by
        rw [hx0]
        funext i
        simp [rectMatMulVec]
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hx0
    apply hxne
    funext j
    exact (vecNorm2_eq_zero_iff x).mp hx0 j
  have hxpos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  apply (div_le_iff₀ hxpos).2
  calc
    vecNorm2 (fun j => xhat j - x j) <=
        lead * (higham21Cond2With A Aplus * vecNorm2 x) +
          theta ^ 2 * Cfinite + eta ^ 2 * CQR := hbound
    _ = (lead * higham21Cond2With A Aplus +
          (theta ^ 2 * Cfinite + eta ^ 2 * CQR) / vecNorm2 x) *
        vecNorm2 x := by
      field_simp [ne_of_gt hxpos]
      ring

end NumStability
