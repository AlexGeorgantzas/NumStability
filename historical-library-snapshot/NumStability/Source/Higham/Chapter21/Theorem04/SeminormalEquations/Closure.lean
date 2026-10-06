import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Foundations.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ComputedOutput.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.EndToEnd
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.Signed
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.TriangularSolves.EnvelopeTransfer
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation11.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.RankStability
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.QRMajorant
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.RemainderBounds
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Signed

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.Closure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete Householder-QR closure for the seminormal-equations path.







namespace NumStability

open scoped BigOperators

/-!
# Concrete signed SNE closure

The analysis-only QR perturbation below is chosen from the proved
implementation-backed Householder panel theorem.  The computed objects remain
the actual panel `Q`, its actual top square `R_hat`, the two rounded triangular
solves, and the rounded final `A^T` action.
-/




























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

























































































































































































































































































































































































































































end NumStability
