-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The final transpose action and forward-error composition for the SNE method.

import NumStability.Algorithms.Underdetermined.Higham21SNEForward
import NumStability.Algorithms.Underdetermined.Higham21RankStability

namespace NumStability

open scoped BigOperators

/-- The exact final `A^T` action applied to the normal-equation vector returned
    by the two rounded triangular solves. -/
noncomputable def higham21SNEExactFormedOutput
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real) (R_hat : Fin m -> Fin m -> Real)
    (b : Fin m -> Real) : Fin n -> Real :=
  rectTransposeMulVec A (higham21SNEComputedNormalSolution fp m R_hat b)

/-- The algorithmic final SNE output, including the rounded matrix-vector
    product used to form `fl(A^T y_hat)`. -/
noncomputable def higham21SNEActualOutput
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real) (R_hat : Fin m -> Fin m -> Real)
    (b : Fin m -> Real) : Fin n -> Real :=
  fl_matVec fp n m (finiteTranspose A)
    (higham21SNEComputedNormalSolution fp m R_hat b)

/-- Transfer the proved componentwise normal-solve envelope through `|A|^T`.
    This is the finite Euclidean envelope available before any additional
    relation between the computed `R_hat` and the rectangular input is used. -/
noncomputable def higham21SNETransferredForwardEnvelope
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (y_hat : Fin m -> Real) : Fin n -> Real :=
  rectTransposeMulVec (absMatrixRect A)
    (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat)

theorem Higham21SNEBackwardCoefficient_nonneg_of_gammaValid
    (fp : FPModel) (m : Nat) (hm1 : gammaValid fp (m + 1)) :
    0 <= Higham21SNEBackwardCoefficient fp m := by
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgm : 0 <= gamma fp m := gamma_nonneg fp hm
  have hgm1 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  dsimp [Higham21SNEBackwardCoefficient]
  nlinarith [sq_nonneg (gamma fp m)]

theorem gamma_le_Higham21SNEBackwardCoefficient
    (fp : FPModel) (m : Nat) (hm1 : gammaValid fp (m + 1)) :
    gamma fp m <= Higham21SNEBackwardCoefficient fp m := by
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgm : 0 <= gamma fp m := gamma_nonneg fp hm
  have hgm1 : 0 <= gamma fp (m + 1) := gamma_nonneg fp hm1
  dsimp [Higham21SNEBackwardCoefficient]
  nlinarith [sq_nonneg (gamma fp m)]

/-- The rounded formation step has the standard componentwise matrix
    backward-error representation

    `x_hat = (A + DeltaA)^T y_hat`, `|DeltaA| <= gamma_m |A|`.

    Unlike the exact-formation definition, this theorem concerns the actual
    `fl_matVec` action in `higham21SNEActualOutput`. -/
theorem higham21_sne_actual_output_formation_backward_error
    (fp : FPModel) (m n : Nat)
    (A : Fin m -> Fin n -> Real) (R_hat : Fin m -> Fin m -> Real)
    (b : Fin m -> Real) (hm : gammaValid fp m) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    ∃ DeltaA : Fin m -> Fin n -> Real,
      (forall i j, |DeltaA i j| <= gamma fp m * |A i j|) /\
      higham21SNEActualOutput fp m n A R_hat b =
        rectTransposeMulVec (fun i j => A i j + DeltaA i j) y_hat := by
  dsimp only
  obtain ⟨DeltaAT, hDeltaAT, hAction⟩ :=
    matVec_backward_error fp n m (finiteTranspose A)
      (higham21SNEComputedNormalSolution fp m R_hat b) hm
  let DeltaA : Fin m -> Fin n -> Real := fun i j => DeltaAT j i
  refine ⟨DeltaA, ?_, ?_⟩
  · intro i j
    simpa [DeltaA, finiteTranspose] using hDeltaAT j i
  · ext j
    have hj := hAction j
    simpa [higham21SNEActualOutput, DeltaA, rectTransposeMulVec,
      finiteTranspose] using hj

/-- A componentwise error bound for the normal-equation vector transfers
    through the exact final `A^T` action. -/
theorem higham21_sne_exact_transpose_error_of_componentwise
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (y y_hat envelope : Fin m -> Real)
    (hcomponentwise : forall i, |y_hat i - y i| <= envelope i) :
    vecNorm2 (fun j =>
      rectTransposeMulVec A y_hat j - rectTransposeMulVec A y j) <=
      vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) := by
  apply vecNorm2_le_of_abs_le
  intro j
  have hsub :=
    congrFun (higham21Eq21_7_rectTransposeMulVec_sub A y_hat y) j
  calc
    |rectTransposeMulVec A y_hat j - rectTransposeMulVec A y j| =
        |rectTransposeMulVec A (fun i => y_hat i - y i) j| := by
          rw [hsub]
    _ <= ∑ i : Fin m, |A i j| * |y_hat i - y i| := by
      simpa [rectTransposeMulVec, finiteTranspose] using
        (abs_rectMatMulVec_le (finiteTranspose A)
          (fun i => y_hat i - y i) j)
    _ <= ∑ i : Fin m, |A i j| * envelope i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcomponentwise i) (abs_nonneg (A i j))
    _ = rectTransposeMulVec (absMatrixRect A) envelope j := by
      simp [rectTransposeMulVec, absMatrixRect]

/-- The exact condition expression `|| |Aplus| |A| ||_2` controls the
    absolute-value transpose action generated by the dual vector
    `Aplus^T x`.  This is the norm bridge needed for the leading error of the
    rounded final matrix-vector product. -/
theorem higham21_sne_dual_majorant_le_cond2
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (x : Fin n -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A)
          (fun i => |rectTransposeMulVec Aplus x i|)) <=
      higham21Cond2With A Aplus * vecNorm2 x := by
  let P : Fin n -> Fin m -> Real := absMatrixRect Aplus
  let B : Fin m -> Fin n -> Real := absMatrixRect A
  let C : Fin n -> Fin n -> Real := rectMatMul P B
  let xabs : Fin n -> Real := fun j => |x j|
  let yabs : Fin m -> Real := fun i => |rectTransposeMulVec Aplus x i|
  let left : Fin n -> Real := rectMatMulVec (finiteTranspose B) yabs
  have hdual : forall i : Fin m,
      yabs i <= rectMatMulVec (finiteTranspose P) xabs i := by
    intro i
    simpa [yabs, xabs, P, rectTransposeMulVec, finiteTranspose,
      absMatrixRect] using
      (abs_rectMatMulVec_le (finiteTranspose Aplus) x i)
  have hleft_nonneg : forall j : Fin n, 0 <= left j := by
    intro j
    simp only [left, rectMatMulVec]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (by simp [B, finiteTranspose, absMatrixRect])
      (by simp [yabs])
  have hleft_le : forall j : Fin n,
      left j <=
        rectMatMulVec (finiteTranspose B)
          (rectMatMulVec (finiteTranspose P) xabs) j := by
    intro j
    simp only [left, rectMatMulVec]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hdual i)
      (by simp [B, finiteTranspose, absMatrixRect])
  have hassoc :=
    higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
      B P xabs
  have hpoint : forall j : Fin n,
      |left j| <= rectMatMulVec (finiteTranspose C) xabs j := by
    intro j
    rw [abs_of_nonneg (hleft_nonneg j)]
    calc
      left j <=
          rectMatMulVec (finiteTranspose B)
            (rectMatMulVec (finiteTranspose P) xabs) j := hleft_le j
      _ = rectMatMulVec (finiteTranspose (rectMatMul P B)) xabs j :=
        congrFun hassoc j
      _ = rectMatMulVec (finiteTranspose C) xabs j := by rfl
  have hC : rectOpNorm2Le C (higham21Cond2With A Aplus) := by
    simpa [C, P, B, higham21Cond2With] using
      (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl)
  have hCT : rectOpNorm2Le (finiteTranspose C)
      (higham21Cond2With A Aplus) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le C
      (higham21Cond2With_nonneg A Aplus) hC
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A)
          (fun i => |rectTransposeMulVec Aplus x i|)) =
        vecNorm2 left := by
          rfl
    _ <= vecNorm2 (rectMatMulVec (finiteTranspose C) xabs) :=
      vecNorm2_le_of_abs_le left
        (rectMatMulVec (finiteTranspose C) xabs) hpoint
    _ <= higham21Cond2With A Aplus * vecNorm2 xabs := hCT xabs
    _ = higham21Cond2With A Aplus * vecNorm2 x := by
      rw [show vecNorm2 xabs = vecNorm2 x by simpa [xabs] using vecNorm2_abs x]

/-- Compose a componentwise normal-solve error with the rounded final
    `fl(A^T y_hat)` formation.  The first term is the exact Chapter 21
    condition expression.  The second term transfers the supplied normal-solve
    envelope through `|A|^T`; its factor `1 + gamma_m` also accounts for using
    `y_hat`, rather than `y`, in the rounded formation. -/
theorem higham21_sne_fl_transpose_forward_error_of_componentwise
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (y y_hat envelope : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hm : gammaValid fp m)
    (hcomponentwise : forall i, |y_hat i - y i| <= envelope i) :
    vecNorm2 (fun j =>
        fl_matVec fp n m (finiteTranspose A) y_hat j -
          rectTransposeMulVec A y j) <=
      gamma fp m * higham21Cond2With A Aplus *
          vecNorm2 (rectTransposeMulVec A y) +
        (1 + gamma fp m) *
          vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) := by
  let x : Fin n -> Real := rectMatMulVec (finiteTranspose A) y
  let exact_hat : Fin n -> Real := rectMatMulVec (finiteTranspose A) y_hat
  let formationError : Fin n -> Real := fun j =>
    fl_matVec fp n m (finiteTranspose A) y_hat j - exact_hat j
  let normalError : Fin n -> Real := fun j => exact_hat j - x j
  let base : Fin n -> Real :=
    rectMatMulVec (finiteTranspose (absMatrixRect A)) (fun i => |y i|)
  let transferred : Fin n -> Real :=
    rectMatMulVec (finiteTranspose (absMatrixRect A)) envelope
  have hgamma_nonneg : 0 <= gamma fp m := gamma_nonneg fp hm
  have hdual : y = rectMatMulVec (finiteTranspose Aplus) x := by
    simpa [x] using
      (higham21_theorem21_1_transpose_left_inverse_of_right_inverse
        A Aplus hRight y).symm
  have hbase : vecNorm2 base <=
      higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [base, hdual, rectTransposeMulVec] using
      (higham21_sne_dual_majorant_le_cond2 A Aplus x)
  have hnormal : vecNorm2 normalError <= vecNorm2 transferred := by
    simpa [normalError, exact_hat, x, transferred, rectTransposeMulVec] using
      (higham21_sne_exact_transpose_error_of_componentwise
        A y y_hat envelope hcomponentwise)
  have hyhat_abs : forall i : Fin m, |y_hat i| <= |y i| + envelope i := by
    intro i
    calc
      |y_hat i| = |(y_hat i - y i) + y i| := by congr 1 <;> ring
      _ <= |y_hat i - y i| + |y i| := abs_add_le _ _
      _ <= envelope i + |y i| :=
        add_le_add_left (hcomponentwise i) _
      _ = |y i| + envelope i := by ring
  have hformation_point : forall j : Fin n,
      |formationError j| <=
        gamma fp m * (base j + transferred j) := by
    intro j
    calc
      |formationError j| <=
          gamma fp m * ∑ i : Fin m, |A i j| * |y_hat i| := by
        simpa [formationError, exact_hat, rectMatMulVec, finiteTranspose] using
          (matVec_error_bound fp n m (finiteTranspose A) y_hat hm j)
      _ <= gamma fp m *
          ∑ i : Fin m, |A i j| * (|y i| + envelope i) := by
        apply mul_le_mul_of_nonneg_left _ hgamma_nonneg
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hyhat_abs i) (abs_nonneg (A i j))
      _ = gamma fp m * (base j + transferred j) := by
        congr 1
        simp only [base, transferred, rectMatMulVec, finiteTranspose,
          absMatrixRect]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hformation : vecNorm2 formationError <=
      gamma fp m * (vecNorm2 base + vecNorm2 transferred) := by
    calc
      vecNorm2 formationError <=
          vecNorm2 (fun j => gamma fp m * (base j + transferred j)) :=
        vecNorm2_le_of_abs_le formationError
          (fun j => gamma fp m * (base j + transferred j)) hformation_point
      _ = gamma fp m * vecNorm2 (fun j => base j + transferred j) := by
        rw [vecNorm2_smul, abs_of_nonneg hgamma_nonneg]
      _ <= gamma fp m * (vecNorm2 base + vecNorm2 transferred) :=
        mul_le_mul_of_nonneg_left (vecNorm2_add_le base transferred)
          hgamma_nonneg
  have hformation_cond : vecNorm2 formationError <=
      gamma fp m *
        (higham21Cond2With A Aplus * vecNorm2 x +
          vecNorm2 transferred) := by
    exact hformation.trans
      (mul_le_mul_of_nonneg_left (add_le_add hbase le_rfl) hgamma_nonneg)
  have hsplit :
      (fun j => fl_matVec fp n m (finiteTranspose A) y_hat j - x j) =
        fun j => formationError j + normalError j := by
    ext j
    simp [formationError, normalError, exact_hat]
  have hfinal :
      vecNorm2 (fun j => fl_matVec fp n m (finiteTranspose A) y_hat j - x j) <=
        gamma fp m * higham21Cond2With A Aplus * vecNorm2 x +
          (1 + gamma fp m) * vecNorm2 transferred := by
    calc
      vecNorm2 (fun j => fl_matVec fp n m (finiteTranspose A) y_hat j - x j) =
          vecNorm2 (fun j => formationError j + normalError j) :=
        congrArg vecNorm2 hsplit
      _ <= vecNorm2 formationError + vecNorm2 normalError :=
        vecNorm2_add_le formationError normalError
      _ <= gamma fp m *
            (higham21Cond2With A Aplus * vecNorm2 x +
              vecNorm2 transferred) + vecNorm2 transferred :=
        add_le_add hformation_cond hnormal
      _ = gamma fp m * higham21Cond2With A Aplus * vecNorm2 x +
          (1 + gamma fp m) * vecNorm2 transferred := by ring
  simpa [x, transferred, rectTransposeMulVec] using hfinal

/-- The existing SNE solve theorem, transferred to the exact final `A^T`
    action and normalized by the exact solution norm. -/
theorem higham21_sne_exact_formed_output_relative_forward_error
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y)) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    let x_hat := higham21SNEExactFormedOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      vecNorm2
          (higham21SNETransferredForwardEnvelope
            fp m n A AAT_inv R_hat y_hat) /
        vecNorm2 x := by
  dsimp only
  have hCore :=
    higham21_sne_computed_forward_error fp m (rectGram A) AAT_inv R_hat
      b y hInv hExact hR_diag hChol hm1
  dsimp only at hCore
  obtain ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩ := hCore
  have hTransferred :=
    higham21_sne_exact_transpose_error_of_componentwise A y
      (higham21SNEComputedNormalSolution fp m R_hat b)
      (higham21SNEForwardEnvelope fp m AAT_inv R_hat
        (higham21SNEComputedNormalSolution fp m R_hat b)) hEnvelope
  have hRelative :=
    div_le_div_of_nonneg_right hTransferred (le_of_lt hx)
  simpa [higham21SNEExactFormedOutput,
    higham21SNETransferredForwardEnvelope] using hRelative

/-- Equation (21.11), SNE side, for the complete computed output.  This is the
    strongest unconditional relative 2-norm statement supplied by the current
    SNE backward-error infrastructure: the rounded final formation contributes
    `gamma_m * cond2(A)`, while the normal-solve error remains as the explicit
    transferred finite envelope. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_envelope
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y)) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      gamma fp m * higham21Cond2With A Aplus +
        (1 + gamma fp m) *
          vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) /
            vecNorm2 x := by
  dsimp only
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hRight :
      rectMatMul A (undetAplusOfGramInv A AAT_inv) = idMatrix m :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_inverse
      A (rectGram A) AAT_inv (by intro i j; rfl) hInv
  have hCore :=
    higham21_sne_computed_forward_error fp m (rectGram A) AAT_inv R_hat
      b y hInv hExact hR_diag hChol hm1
  dsimp only at hCore
  obtain ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩ := hCore
  have hAbsolute :=
    higham21_sne_fl_transpose_forward_error_of_componentwise fp A
      (undetAplusOfGramInv A AAT_inv) y
      (higham21SNEComputedNormalSolution fp m R_hat b)
      (higham21SNEForwardEnvelope fp m AAT_inv R_hat
        (higham21SNEComputedNormalSolution fp m R_hat b))
      hRight hm hEnvelope
  have hxne : vecNorm2 (rectTransposeMulVec A y) ≠ 0 := ne_of_gt hx
  calc
    vecNorm2 (fun j => higham21SNEActualOutput fp m n A R_hat b j -
        rectTransposeMulVec A y j) /
        vecNorm2 (rectTransposeMulVec A y) <=
      (gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b)))) /
        vecNorm2 (rectTransposeMulVec A y) :=
      div_le_div_of_nonneg_right hAbsolute (le_of_lt hx)
    _ = gamma fp m *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) /
          vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]

/-- A finite source-shaped endpoint.  If the transferred normal-solve envelope
    has a first-order `(n-1) * eta * cond2(A)` bound and a finite
    `eta^2 * C` remainder, then the complete rounded output has the printed
    `n * eta * cond2(A)` leading term and the explicit quadratic remainder
    displayed below.

    The transferred-envelope hypothesis is intentionally visible: it is the
    precise QR/SNE estimate not derivable from `sne_backward_error` alone. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic_of_transferred_bound
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (eta C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hn : 0 < n)
    (heta : 0 <= eta)
    (hC : 0 <= C)
    (hgamma_le : gamma fp m <= eta)
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y))
    (hTransferred :
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
      let x := rectTransposeMulVec A y
      let Aplus := undetAplusOfGramInv A AAT_inv
      vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) <=
        ((n : Real) - 1) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * C) :
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      (n : Real) * eta * higham21Cond2With A Aplus +
        eta ^ 2 *
          (((n : Real) - 1) * higham21Cond2With A Aplus * vecNorm2 x +
            (1 + eta) * C) / vecNorm2 x := by
  dsimp only at hTransferred ⊢
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgamma_nonneg : 0 <= gamma fp m := gamma_nonneg fp hm
  have hcond_nonneg :
      0 <= higham21Cond2With A (undetAplusOfGramInv A AAT_inv) :=
    higham21Cond2With_nonneg A (undetAplusOfGramInv A AAT_inv)
  have hxnorm_nonneg : 0 <= vecNorm2 (rectTransposeMulVec A y) :=
    vecNorm2_nonneg _
  have hn_real : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hdim_nonneg : 0 <= (n : Real) - 1 := sub_nonneg.mpr hn_real
  have hbudget_nonneg :
      0 <= ((n : Real) - 1) * eta *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hdim_nonneg heta) hcond_nonneg)
        hxnorm_nonneg)
      (mul_nonneg (sq_nonneg eta) hC)
  have hone_gamma_nonneg : 0 <= 1 + gamma fp m := by linarith
  have hone_le : 1 + gamma fp m <= 1 + eta := by linarith
  have hlead :
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) <=
        eta * higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
          vecNorm2 (rectTransposeMulVec A y) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgamma_le hcond_nonneg) hxnorm_nonneg
  have hscaledTransferred :
      (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) <=
        (1 + eta) *
          (((n : Real) - 1) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) := by
    calc
      (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) <=
          (1 + gamma fp m) *
            (((n : Real) - 1) * eta *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        mul_le_mul_of_nonneg_left hTransferred hone_gamma_nonneg
      _ <= (1 + eta) *
            (((n : Real) - 1) * eta *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        mul_le_mul_of_nonneg_right hone_le hbudget_nonneg
  have hEnvelopeRelative :=
    higham21_eq21_11_sne_actual_output_relative_forward_error_envelope
      fp A AAT_inv R_hat b y hInv hExact hR_diag hChol hm1 hx
  dsimp only at hEnvelopeRelative
  have hxne : vecNorm2 (rectTransposeMulVec A y) ≠ 0 := ne_of_gt hx
  have hAbsoluteShape :
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b))) <=
        (n : Real) * eta *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          eta ^ 2 *
            (((n : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + eta) * C) := by
    calc
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b))) <=
          eta * higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
            (1 + eta) *
              (((n : Real) - 1) * eta *
                    higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                      vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        add_le_add hlead hscaledTransferred
      _ = (n : Real) * eta *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          eta ^ 2 *
            (((n : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + eta) * C) := by ring
  have hRelativeShape :
      (gamma fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + gamma fp m) *
              vecNorm2
                (rectTransposeMulVec (absMatrixRect A)
                  (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                    (higham21SNEComputedNormalSolution fp m R_hat b)))) /
          vecNorm2 (rectTransposeMulVec A y) <=
        ((n : Real) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            eta ^ 2 *
              (((n : Real) - 1) *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                (1 + eta) * C)) /
          vecNorm2 (rectTransposeMulVec A y) :=
    div_le_div_of_nonneg_right hAbsoluteShape (le_of_lt hx)
  calc
    vecNorm2 (fun j => higham21SNEActualOutput fp m n A R_hat b j -
        rectTransposeMulVec A y j) / vecNorm2 (rectTransposeMulVec A y) <=
      gamma fp m *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) /
          vecNorm2 (rectTransposeMulVec A y) := hEnvelopeRelative
    _ = (gamma fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + gamma fp m) *
              vecNorm2
                (rectTransposeMulVec (absMatrixRect A)
                  (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                    (higham21SNEComputedNormalSolution fp m R_hat b)))) /
          vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]
    _ <= ((n : Real) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            eta ^ 2 *
              (((n : Real) - 1) *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                (1 + eta) * C)) /
          vecNorm2 (rectTransposeMulVec A y) := hRelativeShape
    _ = (n : Real) * eta *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        eta ^ 2 *
          (((n : Real) - 1) *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + eta) * C) / vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]

/-- The source-shaped theorem specialized to the finite gamma combination
    returned by `sne_backward_error`.  The remaining hypothesis is exactly the
    unavailable transfer of that solve certificate through `|A|^T` with the
    displayed first-order coefficient and a finite quadratic remainder. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hn : 0 < n)
    (hC : 0 <= C)
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y))
    (hTransferred :
      let eta := Higham21SNEBackwardCoefficient fp m
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
      let x := rectTransposeMulVec A y
      let Aplus := undetAplusOfGramInv A AAT_inv
      vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) <=
        ((n : Real) - 1) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * C) :
    let eta := Higham21SNEBackwardCoefficient fp m
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      (n : Real) * eta * higham21Cond2With A Aplus +
        eta ^ 2 *
          (((n : Real) - 1) * higham21Cond2With A Aplus * vecNorm2 x +
            (1 + eta) * C) / vecNorm2 x := by
  exact
    higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic_of_transferred_bound
      fp A AAT_inv R_hat b y (Higham21SNEBackwardCoefficient fp m) C
      hInv hExact hR_diag hChol hm1 hn
      (Higham21SNEBackwardCoefficient_nonneg_of_gammaValid fp m hm1) hC
      (gamma_le_Higham21SNEBackwardCoefficient fp m hm1) hx hTransferred

end NumStability
