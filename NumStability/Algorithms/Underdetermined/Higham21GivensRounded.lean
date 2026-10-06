-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Rounded stored-Givens application endpoint for Theorem 21.4.

import NumStability.Algorithms.Underdetermined.Higham21Givens

namespace NumStability

/-! ## Stored rotations and their rounded transpose replay -/

/-- One computed Givens rotation retained after the QR sweep.

The coefficients are stored in the orientation used while reducing `A^T`.
The final Q-method action therefore replays the transpose of each rotation. -/
structure Higham21StoredGivensRotation (n : Nat) where
  p : Fin n
  q : Fin n
  distinct : Not (p = q)
  c_hat : Real
  s_hat : Real

/-- Rounded application of the transpose of one stored Givens rotation.

For the repository convention
`G = [[c,s],[-s,c]]`, transposition replaces `s` by `-s`.  Floating-point
negation is exact, so the existing rounded two-coordinate kernel can be
reused directly. -/
noncomputable def Higham21StoredGivensRotation.applyTranspose
    {n : Nat} (fp : FPModel) (g : Higham21StoredGivensRotation n)
    (x : Fin n -> Real) : Fin n -> Real :=
  fl_givensApply fp n g.p g.q g.c_hat (-g.s_hat) x

/-- Replay stored rotations in QR order to apply their transposed product.

If `trace = [G_0,...,G_{r-1}]` is the reduction order, `foldr` computes
`G_0^T (G_1^T (... (G_{r-1}^T z)))`, which is the Q-method action. -/
noncomputable def higham21ApplyStoredGivensRotationsTranspose
    (fp : FPModel) (n : Nat)
    (trace : List (Higham21StoredGivensRotation n))
    (z : Fin n -> Real) : Fin n -> Real :=
  trace.foldr
    (fun g x => Higham21StoredGivensRotation.applyTranspose fp g x) z

/-! ## Fixed-accumulation application interface -/

/-- A per-input certificate for rounded stored-rotation replay.

`Q_hat` may depend on the input vector.  This is the right strength for a
rounded application: it records that this concrete output is an action by a
matrix within Frobenius distance `etaQ` of the fixed exact QR factor.  The
historical Householder name on `HouseholderQRPanelQhatFixedAccumError` is only
a container; its fields are method-independent. -/
structure Higham21GivensFixedAccumulationCertificate
    (fp : FPModel) (n : Nat)
    (Q_ref : Fin n -> Fin n -> Real)
    (trace : List (Higham21StoredGivensRotation n))
    (z : Fin n -> Real) (etaQ : Real) where
  Q_hat : Fin n -> Fin n -> Real
  fixed : HouseholderQRPanelQhatFixedAccumError n Q_ref Q_hat etaQ
  replay_eq :
    higham21ApplyStoredGivensRotationsTranspose fp n trace z =
      matMulVec n Q_hat z

/-- Any fixed-accumulation radius carried by the certificate is nonnegative. -/
theorem higham21_fixed_accumulation_radius_nonneg
    {n : Nat} {Q Q_hat : Fin n -> Fin n -> Real} {etaQ : Real}
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat etaQ) :
    0 <= etaQ := by
  rcases hQerr.result with ⟨DeltaQ, _hrep, hDeltaQ⟩
  exact le_trans (frobNorm_nonneg DeltaQ) hDeltaQ

/-- Global bridge expected from an implementation that retains the staged QR
rotation trace.

This is the sole missing executable bridge in the current upstream API:
`fl_givensQRStageFold` returns only the reduced panel, so it must be extended
to expose the computed coefficients in QR order and prove that reverse
transpose replay satisfies this predicate relative to the same exact factor
selected by `higham21GivensQMethodQ`. -/
def Higham21GivensStoredReplayBridge
    (fp : FPModel) (n : Nat)
    (Q_ref : Fin n -> Fin n -> Real)
    (trace : List (Higham21StoredGivensRotation n))
    (etaQ : Real) : Prop :=
  forall z : Fin n -> Real, exists Q_hat : Fin n -> Fin n -> Real,
    HouseholderQRPanelQhatFixedAccumError n Q_ref Q_hat etaQ /\
    higham21ApplyStoredGivensRotationsTranspose fp n trace z =
      matMulVec n Q_hat z

/-! ## Method-independent rounded-Q handoff -/

/-- Common rowwise coefficient obtained from a QR residual `etaQR`, the
triangular-solve residual `gamma_m`, and a fixed accumulated-Q radius `etaQ`.

The first branch controls the inverse-induced perturbation in the first
system.  The second controls the rounded product in the transpose-range
system. -/
noncomputable def Higham21FixedAccumulationRoundedRowwiseCoefficient
    (fp : FPModel) (m : Nat) (etaQR etaQ : Real) : Real :=
  let etaR := gamma fp m
  let etaBase := etaQR + etaR * (1 + etaQR)
  let qinv := 1 / (1 - etaQ)
  max
    (etaBase + (qinv * etaQ) * (1 + etaBase))
    (etaQR + etaQ * (1 + etaQR))

theorem Higham21FixedAccumulationRoundedRowwiseCoefficient_nonneg
    (fp : FPModel) (m : Nat) (etaQR etaQ : Real)
    (hetaQR : 0 <= etaQR) (hetaQ : 0 <= etaQ) :
    0 <= Higham21FixedAccumulationRoundedRowwiseCoefficient
      fp m etaQR etaQ := by
  have hsecond : 0 <= etaQR + etaQ * (1 + etaQR) :=
    add_nonneg hetaQR
      (mul_nonneg hetaQ (add_nonneg zero_le_one hetaQR))
  exact hsecond.trans (by
    unfold Higham21FixedAccumulationRoundedRowwiseCoefficient
    dsimp
    exact le_max_right _ _)

/-- An upper-triangular square block with nonzero diagonal has an exact
preimage for every vector.  This supplies the coordinate used by the second
perturbed system without referring to a particular QR implementation. -/
theorem higham21_upper_square_exists_exact_preimage
    {m : Nat} (R_hat : Fin m -> Fin m -> Real)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hdiag : forall i : Fin m, Not (R_hat i i = 0))
    (y1 : Fin m -> Real) :
    exists y : Fin m -> Real, rectMatMulVec R_hat y = y1 := by
  have hdet : Not (Matrix.det
      (R_hat : Matrix (Fin m) (Fin m) Real) = 0) :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R_hat hupper hdiag
  have hInverse : IsInverse m R_hat (nonsingInv m R_hat) :=
    isInverse_nonsingInv_of_det_ne_zero m R_hat hdet
  refine ⟨matMulVec m (nonsingInv m R_hat) y1, ?_⟩
  change matMulVec m R_hat (matMulVec m (nonsingInv m R_hat) y1) = y1
  exact matMulVec_of_isRightInverse
    R_hat (nonsingInv m R_hat) hInverse.2 y1

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

/-- Lemma 21.2 turns the two fixed-accumulation systems into rowwise backward
stability for the actual supplied output. -/
theorem higham21_q_method_fixed_accumulation_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real)
    (Q Q_hat : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (b : Fin m -> Real) (x_hat : Fin (m + k) -> Real)
    {etaQR etaQ : Real}
    (hetaQR : 0 <= etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hdiag : forall i : Fin m,
      Not (R_tall (Fin.castAdd k i) i = 0))
    (hvalidTri : gammaValid fp m)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ)
    (hQsmall : etaQ < 1)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hx :
      x_hat = matMulVec (m + k) Q_hat
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun i j => R_tall (Fin.castAdd k i) j)) b)
          (0 : Fin k -> Real)))
    (hCondSmall :
      3 *
        (Higham21FixedAccumulationRoundedRowwiseCoefficient
            fp m etaQR etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (Real.sqrt 2 *
        Higham21FixedAccumulationRoundedRowwiseCoefficient
          fp m etaQR etaQ) := by
  let R_hat : Fin m -> Fin m -> Real := fun i j =>
    R_tall (Fin.castAdd k i) j
  let y1 : Fin m -> Real :=
    fl_forwardSub fp m (matTranspose R_hat) b
  let eta : Real :=
    Higham21FixedAccumulationRoundedRowwiseCoefficient fp m etaQR etaQ
  let Aplus : Fin (m + k) -> Fin m -> Real :=
    undetAplusOfGramNonsingInv A
  let rho : Real :=
    eta * Real.sqrt (((m + k : Nat) : Real)) *
      higham21Cond2With A Aplus
  have hetaQ : 0 <= etaQ :=
    higham21_fixed_accumulation_radius_nonneg hQerr
  have heta : 0 <= eta := by
    exact Higham21FixedAccumulationRoundedRowwiseCoefficient_nonneg
      fp m etaQR etaQ hetaQR hetaQ
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hgram
  obtain ⟨Q_inv, DeltaR, y, _hleft, _hDeltaR,
      hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_q_method_fixed_accumulation_two_perturbed_systems
      fp A Q Q_hat R_tall b x_hat hqr hdiag hvalidTri hQerr hQsmall hx
  let DeltaA1 : Fin m -> Fin (m + k) -> Real :=
    Higham21QMethodDeltaA1 A Q_inv
      (fun i j => R_hat i j + DeltaR i j)
  let DeltaA2 : Fin m -> Fin (m + k) -> Real :=
    Higham21QMethodDeltaA2 A Q_hat R_hat
  have hrow1' : forall i : Fin m,
      rectRowNorm2 DeltaA1 i <= eta * rectRowNorm2 A i := by
    simpa [DeltaA1, R_hat, eta] using hrow1
  have hrow2' : forall i : Fin m,
      rectRowNorm2 DeltaA2 i <= eta * rectRowNorm2 A i := by
    simpa [DeltaA2, R_hat, eta] using hrow2
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA1 Aplus eta heta hrow1'
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA2 Aplus eta heta hrow2'
  have hsmall : 3 * max rho rho < 1 := by
    simpa [rho, eta, Aplus] using hCondSmall
  exact
    higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x_hat y rho rho eta hRight
      (by simpa [DeltaA1, R_hat] using hfirst)
      (by simpa [DeltaA2, R_hat] using hsecond)
      hProd1 hProd2 hsmall heta hrow1' hrow2'

/-! ## Staged-Givens specialization -/

/-- Top square block of the concrete staged Givens `R_hat`. -/
noncomputable def higham21GivensRoundedRTop
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin m -> Fin m -> Real := fun i j =>
  higham21GivensQMethodRTall fp m k A (Fin.castAdd k i) j

/-- Rounded triangular coordinate used as the input to stored-rotation replay. -/
noncomputable def higham21GivensRoundedY1
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin m -> Real :=
  fl_forwardSub fp m (matTranspose (higham21GivensRoundedRTop fp m k A)) b

/-- Actual rounded output obtained by replaying a supplied stored Givens trace. -/
noncomputable def higham21GivensStoredRoundedOutput
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (trace : List (Higham21StoredGivensRotation (m + k))) :
    Fin (m + k) -> Real :=
  higham21ApplyStoredGivensRotationsTranspose fp (m + k) trace
    (Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real))

/-- Per-input fixed-accumulation certificate specialized to the staged Givens
Q-method input and its exact certificate factor. -/
abbrev Higham21GivensQMethodApplicationCertificate
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hvalidGivens : gammaValid fp 8)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    (etaQ : Real) :=
  Higham21GivensFixedAccumulationCertificate fp (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens) trace
    (Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real)) etaQ

/-- Equation (21.10) forward/action error for the actual stored-rotation
replay. -/
theorem higham21_givens_stored_replay_action_error
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hvalidGivens : gammaValid fp 8)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ) :
    vecNorm2 (fun i : Fin (m + k) =>
      higham21GivensStoredRoundedOutput fp m k A b trace i -
        matMulVec (m + k)
          (higham21GivensQMethodQ fp m k A hvalidGivens)
          (Fin.append (higham21GivensRoundedY1 fp m k A b)
            (0 : Fin k -> Real)) i) <=
      etaQ * vecNorm2 (higham21GivensRoundedY1 fp m k A b) := by
  let y1 := higham21GivensRoundedY1 fp m k A b
  let x_hat := higham21GivensStoredRoundedOutput fp m k A b trace
  have hx :
      x_hat = matMulVec (m + k) happ.Q_hat
        (Fin.append y1 (0 : Fin k -> Real)) := by
    simpa [x_hat, y1, higham21GivensStoredRoundedOutput] using happ.replay_eq
  simpa [x_hat, y1] using
    (higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      happ.Q_hat y1 x_hat etaQ happ.fixed hx)

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

/-- Rowwise backward stability of the actual rounded stored-Givens output,
conditional only on the explicit per-input application certificate. -/
theorem higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensStoredRoundedOutput fp m k A b trace)
      (Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ) := by
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
  simpa [Higham21GivensRoundedRowwiseCoefficient] using
    (higham21_q_method_fixed_accumulation_rowwise_backward_stable
      fp A
      (higham21GivensQMethodQ fp m k A hvalidGivens)
      happ.Q_hat
      (higham21GivensQMethodRTall fp m k A)
      b (higham21GivensStoredRoundedOutput fp m k A b trace)
      (higham21_givens_qr_gamma_tilde_nonneg
        fp (m + k) m hvalidGivens)
      hqr hdiag' hvalidTri happ.fixed hQsmall hgram hx
      (by simpa [Higham21GivensRoundedRowwiseCoefficient] using hCondSmall))

/-- Printed `omega^R` consequence for the actual rounded stored-Givens
output. -/
theorem higham21_theorem21_4_givens_stored_replay_omegaR_le
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensStoredRoundedOutput fp m k A b trace) <=
      Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ := by
  exact
    higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
      (higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
        fp A b hm hvalidGivens hdiag hvalidTri hgram trace happ
        hQsmall hCondSmall)

/-- Staged-Givens specialization of the global stored-replay bridge. -/
def Higham21GivensQMethodStoredReplayBridge
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (hvalidGivens : gammaValid fp 8)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    (etaQ : Real) : Prop :=
  Higham21GivensStoredReplayBridge fp (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens) trace etaQ

/-- Strongest executable endpoint available from the current API: once the
single stored-replay bridge is supplied, the concrete trace replay is rowwise
backward stable. -/
theorem higham21_theorem21_4_givens_stored_replay_rowwise_of_bridge
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (hbridge : Higham21GivensQMethodStoredReplayBridge
      fp m k A hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (higham21GivensStoredRoundedOutput fp m k A b trace)
      (Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ) := by
  let z : Fin (m + k) -> Real :=
    Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real)
  obtain ⟨Q_hat, hfixed, hreplay⟩ := hbridge z
  let happ : Higham21GivensQMethodApplicationCertificate
      fp m k A b hvalidGivens trace etaQ :=
    { Q_hat := Q_hat
      fixed := hfixed
      replay_eq := by simpa [z] using hreplay }
  exact
    higham21_theorem21_4_givens_stored_replay_rowwise_backward_stable
      fp A b hm hvalidGivens hdiag hvalidTri hgram trace happ
      hQsmall hCondSmall

/-- Printed `omega^R` endpoint under the sole global replay bridge. -/
theorem higham21_theorem21_4_givens_stored_replay_omegaR_le_of_bridge
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidGivens : gammaValid fp 8)
    (hdiag : forall i : Fin m,
      Not (higham21GivensRoundedRTop fp m k A i i = 0))
    (hvalidTri : gammaValid fp m)
    (hgram : Not (Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (trace : List (Higham21StoredGivensRotation (m + k)))
    {etaQ : Real}
    (hbridge : Higham21GivensQMethodStoredReplayBridge
      fp m k A hvalidGivens trace etaQ)
    (hQsmall : etaQ < 1)
    (hCondSmall :
      3 *
        (Higham21GivensRoundedRowwiseCoefficient fp m k etaQ *
          Real.sqrt (((m + k : Nat) : Real)) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    higham21RowwiseBackwardErrorOmegaR A b
        (higham21GivensStoredRoundedOutput fp m k A b trace) <=
      Real.sqrt 2 *
        Higham21GivensRoundedRowwiseCoefficient fp m k etaQ := by
  exact
    higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
      (higham21_theorem21_4_givens_stored_replay_rowwise_of_bridge
        fp A b hm hvalidGivens hdiag hvalidTri hgram trace hbridge
        hQsmall hCondSmall)

end NumStability
