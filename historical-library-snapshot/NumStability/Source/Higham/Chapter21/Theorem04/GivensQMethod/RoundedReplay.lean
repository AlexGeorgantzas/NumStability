import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.BackwardError.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.RoundedReplay
import NumStability.Algorithms.LinearSystems.Underdetermined.RankStability.FullRowRank.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter21.Theorem04.GivensQMethod.Core
import NumStability.Source.Higham.Chapter21.Theorem04.HouseholderQMethod.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError

/-!
# Source.Higham.Chapter21.Theorem04.GivensQMethod.RoundedReplay

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Rounded stored-Givens application endpoint for Theorem 21.4.



namespace NumStability

/-! ## Stored rotations and their rounded transpose replay -/


































/-! ## Fixed-accumulation application interface -/













































/-! ## Method-independent rounded-Q handoff -/
















































/-- The fixed-accumulation interface constructs both exact perturbed systems
used by Lemma 21.2, together with one common row-relative radius.

This theorem is independent of how `Q_hat` was produced.  A stored Givens
replay enters only through `hx` and `hQerr`. -/
theorem higham21_q_method_fixed_accumulation_two_perturbed_systems
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (Q Q_hat : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (b : Fin m -> Real) (x_hat : Fin (m + k) -> Real)
    {etaQR etaQ : Real}
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hdiag : forall i : Fin m,
      Not (R_tall (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ)
    (hsmall : etaQ < 1)
    (hx :
      x_hat = matMulVec (m + k) Q_hat
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun i j => R_tall (Fin.castAdd k i) j)) b)
          (0 : Fin k -> Real))) :
    let R_hat : Fin m -> Fin m -> Real := fun i j =>
      R_tall (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let eta := Higham21FixedAccumulationRoundedRowwiseCoefficient
      fp m etaQR etaQ
    exists (Q_inv : Fin (m + k) -> Fin (m + k) -> Real)
        (DeltaR : Fin m -> Fin m -> Real) (y : Fin m -> Real),
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) /\
      (forall i j, |DeltaR i j| <= gamma fp m * |R_hat i j|) /\
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b /\
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y /\
      (forall i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i <=
          eta * rectRowNorm2 A i) /\
      forall i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i <=
          eta * rectRowNorm2 A i := by
  dsimp only
  let R_hat : Fin m -> Fin m -> Real := fun i j =>
    R_tall (Fin.castAdd k i) j
  let y1 : Fin m -> Real :=
    fl_forwardSub fp m (matTranspose R_hat) b
  let etaR : Real := gamma fp m
  let etaBase : Real := etaQR + etaR * (1 + etaQR)
  let qinv : Real := 1 / (1 - etaQ)
  let eta1 : Real := etaBase + (qinv * etaQ) * (1 + etaBase)
  let eta2 : Real := etaQR + etaQ * (1 + etaQR)
  let eta : Real :=
    Higham21FixedAccumulationRoundedRowwiseCoefficient fp m etaQR etaQ
  have hRblock : R_tall = lsQRTallBlock (k := k) R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_of_upper_trapezoidal R_tall hqr.upper
  have hupper : IsUpperTrapezoidal m m R_hat :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R_tall hqr.upper
  have hdiag' : forall i : Fin m, Not (R_hat i i = 0) := by
    simpa [R_hat] using hdiag
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag' hupper hvalidTri
  let R_plus : Fin m -> Fin m -> Real :=
    fun i j => R_hat i j + DeltaR i j
  have htri : forall j : Fin m,
      (Finset.univ.sum fun i : Fin m => R_plus i j * y1 i) = b j := by
    intro j
    simpa [R_plus, y1, matMulVec, matTranspose] using hsolve j
  obtain ⟨y, hRy⟩ :=
    higham21_upper_square_exists_exact_preimage R_hat hupper hdiag' y1
  obtain ⟨Q_inv, hleft, hQinvOp⟩ :=
    higham21_qhat_exists_left_inverse_with_opNorm2Le_of_fixed_accum_error_lt_one
      hQerr hsmall
  have hqinv : 0 <= qinv := by
    exact (one_div_pos.mpr (sub_pos.mpr hsmall)).le
  have hx' :
      x_hat = matMulVec (m + k) Q_hat
        (Fin.append y1 (0 : Fin k -> Real)) := by
    simpa [R_hat, y1] using hx
  have hfirst :
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv R_plus i j)
          x_hat = b :=
    Higham21QMethodDeltaA1.system_eq
      A Q_inv Q_hat R_plus b y1 x_hat hleft htri hx'
  have hsecond :
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y :=
    Higham21QMethodDeltaA2.transpose_representation
      A Q_hat R_hat y y1 x_hat hRy hx'
  have hrow1Raw : forall i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv R_plus) i <=
        eta1 * rectRowNorm2 A i := by
    simpa [R_plus, eta1, etaBase, qinv, etaR] using
      (Higham21QMethodDeltaA1.row_bound_of_qr_transpose_certificate
        A Q Q_hat Q_inv R_tall R_hat DeltaR hRblock
        (gamma_nonneg fp hvalidTri) hqinv hqr hDeltaR hQerr hleft hQinvOp)
  have hrow2Raw : forall i : Fin m,
      rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i <=
        eta2 * rectRowNorm2 A i := by
    simpa [eta2] using
      (Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
        A Q Q_hat R_tall R_hat hRblock hqr hQerr)
  have heta_eq : eta = max eta1 eta2 := by
    simp [eta, eta1, eta2, etaBase, qinv, etaR,
      Higham21FixedAccumulationRoundedRowwiseCoefficient]
  have heta1_le : eta1 <= eta := by
    rw [heta_eq]
    exact le_max_left _ _
  have heta2_le : eta2 <= eta := by
    rw [heta_eq]
    exact le_max_right _ _
  have hrow1 : forall i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv R_plus) i <=
        eta * rectRowNorm2 A i := by
    intro i
    exact (hrow1Raw i).trans
      (mul_le_mul_of_nonneg_right heta1_le (rectRowNorm2_nonneg A i))
  have hrow2 : forall i : Fin m,
      rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i <=
        eta * rectRowNorm2 A i := by
    intro i
    exact (hrow2Raw i).trans
      (mul_le_mul_of_nonneg_right heta2_le (rectRowNorm2_nonneg A i))
  refine ⟨Q_inv, DeltaR, y, hleft, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [R_hat, etaR] using hDeltaR
  · simpa [R_hat, R_plus] using hfirst
  · simpa [R_hat] using hsecond
  · simpa [R_hat, R_plus, eta] using hrow1
  · simpa [R_hat, eta] using hrow2


























































































/-! ## Staged-Givens specialization -/


































































/-- Rounded Givens rowwise coefficient before the final `sqrt 2` factor from
Lemma 21.2. -/
noncomputable def Higham21GivensRoundedRowwiseCoefficient
    (fp : FPModel) (m k : Nat) (etaQ : Real) : Real :=
  Higham21FixedAccumulationRoundedRowwiseCoefficient fp m
    (H19.Theorem19_10.gamma_tilde fp (m + k) m) etaQ

theorem Higham21GivensRoundedRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : Nat) (etaQ : Real)
    (hvalidGivens : gammaValid fp 8) (hetaQ : 0 <= etaQ) :
    0 <= Higham21GivensRoundedRowwiseCoefficient fp m k etaQ := by
  exact
    Higham21FixedAccumulationRoundedRowwiseCoefficient_nonneg
      fp m (H19.Theorem19_10.gamma_tilde fp (m + k) m) etaQ
      (higham21_givens_qr_gamma_tilde_nonneg
        fp (m + k) m hvalidGivens)
      hetaQ

/-- The two exact perturbed systems, with common row bounds, for the actual
stored-Givens replay output. -/
theorem higham21_theorem21_4_givens_stored_replay_two_perturbed_systems
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ)
    (hsmall : etaQ < 1) :
    let R_hat := higham21GivensRoundedRTop fp m k A
    let x_hat := higham21GivensStoredRoundedOutput fp m k A b trace
    let eta := Higham21GivensRoundedRowwiseCoefficient fp m k etaQ
    exists (Q_inv : Fin (m + k) -> Fin (m + k) -> Real)
        (DeltaR : Fin m -> Fin m -> Real) (y : Fin m -> Real),
      matMul (m + k) Q_inv happ.Q_hat = idMatrix (m + k) /\
      (forall i j, |DeltaR i j| <= gamma fp m * |R_hat i j|) /\
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b /\
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A happ.Q_hat R_hat i j) y /\
      (forall i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i <=
          eta * rectRowNorm2 A i) /\
      forall i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A happ.Q_hat R_hat) i <=
          eta * rectRowNorm2 A i := by
  have hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A)
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      (higham21GivensQMethodRTall fp m k A)
      (H19.Theorem19_10.gamma_tilde fp (m + k) m) :=
    higham21_givens_qr_backward_error_to_generic_certificate
      (higham21_givens_qr_transpose_certificate
        fp A hm hvalidGivens)
  have hdiag' : forall i : Fin m,
      Not (higham21GivensQMethodRTall fp m k A
        (Fin.castAdd k i) i = 0) := by
    simpa [higham21GivensRoundedRTop] using hdiag
  have hx :
      higham21GivensStoredRoundedOutput fp m k A b trace =
        matMulVec (m + k) happ.Q_hat
          (Fin.append
            (fl_forwardSub fp m
              (matTranspose
                (fun i j => higham21GivensQMethodRTall fp m k A
                  (Fin.castAdd k i) j)) b)
            (0 : Fin k -> Real)) := by
    simpa [higham21GivensStoredRoundedOutput,
      higham21GivensRoundedY1, higham21GivensRoundedRTop] using
      happ.replay_eq
  simpa [higham21GivensRoundedRTop,
    Higham21GivensRoundedRowwiseCoefficient] using
    (higham21_q_method_fixed_accumulation_two_perturbed_systems
      fp A
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      happ.Q_hat
      (higham21GivensQMethodRTall fp m k A)
      b (higham21GivensStoredRoundedOutput fp m k A b trace)
      hqr hdiag' hvalidTri happ.fixed hsmall hx)

















































































































































































end NumStability
