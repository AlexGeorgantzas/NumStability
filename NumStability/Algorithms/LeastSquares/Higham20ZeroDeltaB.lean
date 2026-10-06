import NumStability.Algorithms.LeastSquares.Higham20Theorem20_3
import NumStability.Algorithms.QR.Higham19Labels
import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

namespace Theorem20_3_ZeroDeltaB

/-!
# Higham, Chapter 20, p. 385: the `Δb = 0` variant

The inverse-transpose argument used for a square QR solve needs one additional
piece in the rectangular least-squares case.  After the rounded right-hand-side
transform has been written as `ĉ = P b`, put `N = P⁻¹` and `W = NᵀN`.  The
columns `[T;0]` must be replaced by the graph `[T;L]` which is `W`-orthogonal
to the bottom coordinate subspace.  The graph is explicit:

`L = -((Wbb⁻¹)ᵀ Wbt T)`.

The exact algebra below isolates and proves this rectangular step.  It is the
part absent from the square equation-(19.14) argument.
-/

/-- Top-left block of a matrix indexed by `Fin (n + k)`. -/
noncomputable def topTop {n k : ℕ}
    (M : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M (Fin.castAdd k i) (Fin.castAdd k j)

/-- Bottom-right block of a matrix indexed by `Fin (n + k)`. -/
noncomputable def bottomBottom {n k : ℕ}
    (M : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => M (Fin.natAdd n i) (Fin.natAdd n j)

/-- Bottom-left block of a matrix indexed by `Fin (n + k)`. -/
noncomputable def bottomTop {n k : ℕ}
    (M : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) : Matrix (Fin k) (Fin n) ℝ :=
  fun i j => M (Fin.natAdd n i) (Fin.castAdd k j)

/-- Top-right block of a matrix indexed by `Fin (n + k)`. -/
noncomputable def topBottom {n k : ℕ}
    (M : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j => M (Fin.castAdd k i) (Fin.natAdd n j)

/-- A square top block stacked on top of a rectangular bottom block. -/
noncomputable def stack {n k : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin (n + k)) (Fin n) ℝ :=
  fun i j => Fin.append (fun r : Fin n => T r j) (fun r : Fin k => L r j) i

@[simp] theorem stack_top {n k : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin k) (Fin n) ℝ)
    (i j : Fin n) :
    stack T L (Fin.castAdd k i) j = T i j := by
  simp [stack, Fin.append_left]

@[simp] theorem stack_bottom {n k : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin k) (Fin n) ℝ)
    (i : Fin k) (j : Fin n) :
    stack T L (Fin.natAdd n i) j = L i j := by
  simp [stack, Fin.append_right]

/-- The metric induced by applying an inverse coordinate transform. -/
noncomputable def inverseMetric {m : ℕ}
    (N : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  N.transpose * N

theorem inverseMetric_symmetric {m : ℕ}
    (N : Matrix (Fin m) (Fin m) ℝ) :
    (inverseMetric N).transpose = inverseMetric N := by
  simp [inverseMetric, Matrix.transpose_mul]

/-- The bottom graph which makes `[T;L]` orthogonal, in the `NᵀN` metric,
to the bottom coordinate subspace. -/
noncomputable def metricGraphBottom {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin k) (Fin n) ℝ :=
  -((bottomBottom W)⁻¹).transpose * bottomTop W * T

/-- The linear graph operator before it is applied to the triangular block. -/
noncomputable def metricGraphOperator {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) :
    Matrix (Fin k) (Fin n) ℝ :=
  -((bottomBottom W)⁻¹).transpose * bottomTop W

theorem metricGraphBottom_eq_operator_mul {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    metricGraphBottom W T = metricGraphOperator W * T := by
  simp [metricGraphBottom, metricGraphOperator, Matrix.mul_assoc]

/-- Rectangular vector-action norm predicate. -/
def RectOpNorm2Le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, vecNorm2 (rectMatMulVec M x) ≤ c * vecNorm2 x

/-- The square transform `P = (Q + D)ᵀ` supplied by the `(Q+ΔQ)ᵀ b`
rewriting of the rounded Householder RHS transform. -/
noncomputable def rhsTransformMatrix {m : ℕ}
    (Q D : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => Q j i + D j i

/-- Matrix inverse with its matrix instance fixed explicitly (avoiding the
pointwise inverse instance inherited from the function representation). -/
noncomputable def squareInverse {m : ℕ}
    (P : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  P⁻¹

/-- Relative size of the Householder RHS perturbation used by Theorem 20.3. -/
noncomputable def rhsRadius (fp : FPModel) (m n : ℕ) : ℝ :=
  Theorem20_3.rhsCoeff fp m n

/-- Neumann-series envelope for `P⁻¹`. -/
noncomputable def inverseEnvelope (fp : FPModel) (m n : ℕ) : ℝ :=
  (1 - rhsRadius fp m n)⁻¹

/-- Neumann-series envelope for `P⁻¹-Q`. -/
noncomputable def inverseDifferenceEnvelope (fp : FPModel) (m n : ℕ) : ℝ :=
  rhsRadius fp m n / (1 - rhsRadius fp m n)

/-- Envelope for `‖NᵀN-I‖`, where `N=P⁻¹`. -/
noncomputable def metricDefectEnvelope (fp : FPModel) (m n : ℕ) : ℝ :=
  rhsRadius fp m n * (2 - rhsRadius fp m n) /
    (1 - rhsRadius fp m n) ^ 2

/-- Neumann-series envelope for the rectangular bottom graph operator. -/
noncomputable def graphEnvelope (fp : FPModel) (m n : ℕ) : ℝ :=
  metricDefectEnvelope fp m n / (1 - metricDefectEnvelope fp m n)

/-- A Frobenius perturbation strictly smaller than one makes the explicit
inverse-transpose RHS transform nonsingular and supplies the two Neumann
action bounds used by the metric construction. -/
theorem rhsTransform_unit_inverse_and_difference_actions
    (fp : FPModel) {m n : ℕ}
    (Q D : Matrix (Fin m) (Fin m) ℝ)
    (hQ : IsOrthogonal m Q)
    (hD : frobNorm D ≤ rhsRadius fp m n)
    (hrho : rhsRadius fp m n < 1) :
    IsUnit (rhsTransformMatrix Q D).det ∧
      opNorm2Le (squareInverse (rhsTransformMatrix Q D))
        (inverseEnvelope fp m n) ∧
      opNorm2Le
        (fun i j => squareInverse (rhsTransformMatrix Q D) i j - Q i j)
        (inverseDifferenceEnvelope fp m n) := by
  let rho : ℝ := rhsRadius fp m n
  let P : Matrix (Fin m) (Fin m) ℝ := rhsTransformMatrix Q D
  let N : Matrix (Fin m) (Fin m) ℝ := squareInverse P
  let Qt : Fin m → Fin m → ℝ := matTranspose Q
  let Dt : Fin m → Fin m → ℝ := matTranspose D
  let nu : ℝ := 1 / (1 - rho)
  have hDt : frobNorm Dt ≤ rho := by
    simpa [Dt, rho, frobNorm_transpose] using hD
  have hfixed : HouseholderQRPanelQhatFixedAccumError m Qt P rho := by
    refine ⟨?_, ?_⟩
    · simpa [Qt] using hQ.transpose
    · refine ⟨Dt, ?_, hDt⟩
      intro i j
      rfl
  obtain ⟨B, hBP⟩ :=
    higham21_qhat_exists_left_inverse_of_fixed_accum_error_lt_one
      hfixed (by simpa [rho] using hrho)
  let BM : Matrix (Fin m) (Fin m) ℝ := fun i j => B i j
  have hBPmat :
      BM * P = 1 := by
    ext i j
    have hij := congrFun (congrFun hBP i) j
    simpa [matMul, idMatrix, Matrix.mul_apply] using hij
  have hPunit : IsUnit P.det := Matrix.isUnit_det_of_left_inverse hBPmat
  have hNPmat : N * P = 1 := by
    simpa [N, squareInverse] using Matrix.nonsing_inv_mul P hPunit
  have hNP : matMul m N P = idMatrix m := by
    ext i j
    have hij := congrFun (congrFun hNPmat i) j
    simpa [matMul, idMatrix, Matrix.mul_apply] using hij
  have hNPleft : IsLeftInverse m P N := by
    intro i j
    have hij := congrFun (congrFun hNP i) j
    simpa [matMul, idMatrix] using hij
  have hNraw : opNorm2Le N nu :=
    higham21_qhat_inverse_opNorm2Le_of_frobNorm_lt_one
      Qt P N Dt rho hQ.transpose
      (by
        ext i j
        rfl)
      hDt (by simpa [rho] using hrho) hNPleft
  have hnu0 : 0 ≤ nu :=
    (one_div_pos.mpr (sub_pos.mpr (by simpa [rho] using hrho))).le
  have hEtRaw :
      opNorm2Le (fun i j => N j i - Q j i) (nu * rho) := by
    simpa [Qt, Dt] using
      (higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
        Qt P N Dt rho nu hQ.transpose
        (by
          ext i j
          rfl)
        hDt hNP hnu0 hNraw)
  have hrho0 : 0 ≤ rho := le_trans (frobNorm_nonneg D) (by simpa [rho] using hD)
  have hEraw : opNorm2Le (fun i j => N i j - Q i j) (nu * rho) := by
    have ht := opNorm2Le_transpose
      (fun i j => N j i - Q j i) (mul_nonneg hnu0 hrho0) hEtRaw
    simpa [matTranspose] using ht
  refine ⟨by simpa [P] using hPunit, ?_, ?_⟩
  · simpa [N, P, nu, rho, inverseEnvelope, one_div] using hNraw
  · have hcoeff : nu * rho = inverseDifferenceEnvelope fp m n := by
      simp [nu, rho, inverseDifferenceEnvelope, div_eq_mul_inv, mul_comm]
    rw [← hcoeff]
    simpa [N, P] using hEraw

/-- If `N` is close to an orthogonal `Q`, then the inverse metric `NᵀN`
is close to the identity.  The factorization
`NᵀN-I = (N-Q)ᵀN + Qᵀ(N-Q)` avoids a quadratic overestimate. -/
theorem inverseMetric_defect_action_of_inverse_actions
    {m : ℕ} (N Q : Matrix (Fin m) (Fin m) ℝ) {nu xi : ℝ}
    (hQ : IsOrthogonal m Q)
    (hxi0 : 0 ≤ xi)
    (hN : opNorm2Le N nu)
    (hE : opNorm2Le (fun i j => N i j - Q i j) xi) :
    opNorm2Le
      (fun i j => inverseMetric N i j - idMatrix m i j)
      (xi * nu + xi) := by
  let E : Fin m → Fin m → ℝ := fun i j => N i j - Q i j
  have hEt : opNorm2Le (matTranspose E) xi := by
    exact opNorm2Le_transpose E hxi0 (by simpa [E] using hE)
  have hfirstRect :
      rectOpNorm2Le (matMul m (matTranspose E) N) (xi * nu) :=
    rectOpNorm2Le_matMul_square (matTranspose E) N hxi0 hEt hN
  have hsecondRaw :
      rectOpNorm2Le (matMul m (matTranspose Q) E) ((1 : ℝ) * xi) :=
    rectOpNorm2Le_matMul_square (matTranspose Q) E (by norm_num)
      hQ.transpose_opNorm2Le_one (by simpa [E] using hE)
  have hsecondRect :
      rectOpNorm2Le (matMul m (matTranspose Q) E) xi := by
    simpa only [one_mul] using hsecondRaw
  have hsum :
      opNorm2Le
        (fun i j =>
          matMul m (matTranspose E) N i j +
            matMul m (matTranspose Q) E i j)
        (xi * nu + xi) :=
    opNorm2Le_of_rectOpNorm2Le_square _
      (rectOpNorm2Le_add _ _ hfirstRect hsecondRect)
  have hdecomp :
      (fun i j => inverseMetric N i j - idMatrix m i j) =
        (fun i j =>
          matMul m (matTranspose E) N i j +
            matMul m (matTranspose Q) E i j) := by
    ext i j
    change
      (∑ r : Fin m, N r i * N r j) - (if i = j then 1 else 0) =
        (∑ r : Fin m, (N r i - Q r i) * N r j) +
          ∑ r : Fin m, Q r i * (N r j - Q r j)
    rw [← hQ.left_inv i j]
    simp only [matTranspose, Finset.sum_sub_distrib, sub_mul, mul_sub]
    ring
  rw [hdecomp]
  exact hsum

/-- A principal bottom block inherits the action bound of a square matrix
defect by zero-extending the test vector and projecting the result. -/
theorem bottomBottom_defect_action_of_full_defect_action
    {n k : ℕ} (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) {delta : ℝ}
    (hW : opNorm2Le
      (fun i j => W i j - idMatrix (n + k) i j) delta) :
    opNorm2Le
      (fun i j => bottomBottom W i j - idMatrix k i j) delta := by
  intro x
  let z : Fin (n + k) → ℝ := Fin.append (0 : Fin n → ℝ) x
  let y : Fin (n + k) → ℝ :=
    matMulVec (n + k) (fun i j => W i j - idMatrix (n + k) i j) z
  let yt : Fin n → ℝ := fun i => y (Fin.castAdd k i)
  let yb : Fin k → ℝ :=
    matMulVec k (fun i j => bottomBottom W i j - idMatrix k i j) x
  have hy : y = Fin.append yt yb := by
    funext i
    refine Fin.addCases (motive := fun i : Fin (n + k) =>
      y i = Fin.append yt yb i) ?_ ?_ i
    · intro r
      simp [y, yt, Fin.append_left]
    · intro r
      simp only [Fin.append_right]
      dsimp [y, yb, z, matMulVec, bottomBottom]
      rw [Fin.sum_univ_add]
      simp [idMatrix]
  have hz : vecNorm2 z = vecNorm2 x := by
    unfold vecNorm2
    rw [show z = Fin.append (0 : Fin n → ℝ) x by rfl,
      lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 yb ≤ vecNorm2 (Fin.append yt yb) :=
      lsVecNorm2_right_le_append yt yb
    _ = vecNorm2 y := by rw [hy]
    _ ≤ delta * vecNorm2 z := hW z
    _ = delta * vecNorm2 x := by rw [hz]

/-- The bottom-left block inherits the full metric-defect action bound: the
identity has a zero bottom-left block, so only zero-extension/projection is
needed. -/
theorem bottomTop_action_of_full_defect_action
    {n k : ℕ} (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) {delta : ℝ}
    (hW : opNorm2Le
      (fun i j => W i j - idMatrix (n + k) i j) delta) :
    RectOpNorm2Le (bottomTop W) delta := by
  intro x
  let z : Fin (n + k) → ℝ := Fin.append x (0 : Fin k → ℝ)
  let y : Fin (n + k) → ℝ :=
    matMulVec (n + k) (fun i j => W i j - idMatrix (n + k) i j) z
  let yt : Fin n → ℝ := fun i => y (Fin.castAdd k i)
  let yb : Fin k → ℝ := rectMatMulVec (bottomTop W) x
  have hy : y = Fin.append yt yb := by
    funext i
    refine Fin.addCases (motive := fun i : Fin (n + k) =>
      y i = Fin.append yt yb i) ?_ ?_ i
    · intro r
      simp [y, yt, Fin.append_left]
    · intro r
      simp only [Fin.append_right]
      dsimp [y, yb, z, matMulVec, rectMatMulVec, bottomTop]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have hne :
          (Fin.natAdd n r : Fin (n + k)) ≠ Fin.castAdd k j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      simp [idMatrix, hne]
  have hz : vecNorm2 z = vecNorm2 x := by
    unfold vecNorm2
    rw [show z = Fin.append x (0 : Fin k → ℝ) by rfl,
      lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 yb ≤ vecNorm2 (Fin.append yt yb) :=
      lsVecNorm2_right_le_append yt yb
    _ = vecNorm2 y := by rw [hy]
    _ ≤ delta * vecNorm2 z := hW z
    _ = delta * vecNorm2 x := by rw [hz]

/-- Operator-norm Neumann lemma in the exact form needed by the bottom metric
block.  It proves both determinant nonsingularity and the action bound for the
canonical matrix inverse. -/
theorem identity_perturbation_unit_and_inverse_action
    {k : ℕ} (B : Matrix (Fin k) (Fin k) ℝ) {delta : ℝ}
    (hB : opNorm2Le (fun i j => B i j - idMatrix k i j) delta)
    (hdelta : delta < 1) :
    IsUnit B.det ∧
      opNorm2Le (squareInverse B) (1 / (1 - delta)) := by
  let E : Fin k → Fin k → ℝ := fun i j => B i j - idMatrix k i j
  have hEop : opNorm2Le E delta := by simpa [E] using hB
  have hErect : rectOpNorm2Le E delta :=
    rectOpNorm2Le_of_opNorm2Le_square E hEop
  have hlowerId : ∀ x : Fin k → ℝ,
      (1 : ℝ) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec (idMatrix k) x) := by
    intro x
    simp [rectMatMulVec_idMatrix]
  have hinjAdd : Function.Injective
      (rectMatMulVec (fun i j => idMatrix k i j + E i j)) :=
    rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
      hlowerId hErect hdelta
  have hBrep : (fun i j => idMatrix k i j + E i j) = B := by
    ext i j
    simp [E]
  have hinj : Function.Injective (rectMatMulVec B) := by
    simpa [hBrep] using hinjAdd
  obtain ⟨L, hLB⟩ :=
    ch7_exists_rect_left_inverse_of_rectMatMulVec_injective B hinj
  let LM : Matrix (Fin k) (Fin k) ℝ := fun i j => L i j
  have hLBmat : LM * B = 1 := by
    ext i j
    simpa [LM, Matrix.mul_apply, idMatrix] using hLB i j
  have hunit : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hLBmat
  let Binv : Matrix (Fin k) (Fin k) ℝ := squareInverse B
  have hleft : IsLeftInverse k B Binv := by
    have hmat : Binv * B = 1 := by
      simpa [Binv, squareInverse] using Matrix.nonsing_inv_mul B hunit
    intro i j
    have hij := congrFun (congrFun hmat i) j
    simpa [Matrix.mul_apply, idMatrix] using hij
  have hright : IsRightInverse k B Binv :=
    ch7_isRightInverse_of_isLeftInverse hleft
  have hlower : ∀ x : Fin k → ℝ,
      (1 - delta) * vecNorm2 x ≤ vecNorm2 (matMulVec k B x) := by
    intro x
    have haction :
        matMulVec k B x =
          fun i => matMulVec k (idMatrix k) x i + matMulVec k E x i := by
      rw [← hBrep]
      exact matMulVec_add_left k (idMatrix k) E x
    have hcancel :
        (fun i => matMulVec k B x i + -matMulVec k E x i) = x := by
      ext i
      rw [congrFun haction i]
      simp [matMulVec_id]
    have htri :=
      vecNorm2_add_le (matMulVec k B x) (fun i => -matMulVec k E x i)
    rw [hcancel, vecNorm2_neg] at htri
    calc
      (1 - delta) * vecNorm2 x =
          vecNorm2 x - delta * vecNorm2 x := by ring
      _ ≤ vecNorm2 x - vecNorm2 (matMulVec k E x) :=
        sub_le_sub_left (hEop x) _
      _ ≤ vecNorm2 (matMulVec k B x) :=
        (sub_le_iff_le_add).2 htri
  have hden : 0 < 1 - delta := sub_pos.mpr hdelta
  refine ⟨hunit, ?_⟩
  intro y
  have hbound := hlower (matMulVec k Binv y)
  rw [matMulVec_of_isRightInverse B Binv hright y] at hbound
  calc
    vecNorm2 (matMulVec k (squareInverse B) y) =
        ((1 - delta) * vecNorm2 (matMulVec k Binv y)) /
          (1 - delta) := by
      simp only [Binv]
      field_simp [ne_of_gt hden]
    _ ≤ vecNorm2 y / (1 - delta) :=
      (div_le_div_iff_of_pos_right hden).2 hbound
    _ = (1 / (1 - delta)) * vecNorm2 y := by
      simp only [div_eq_mul_inv, one_mul, mul_comm]

/-- Composition estimate for the explicit bottom metric graph. -/
theorem metricGraphOperator_action_of_block_actions
    {n k : ℕ} (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    {mu delta : ℝ}
    (hmu0 : 0 ≤ mu)
    (hBinv : opNorm2Le (squareInverse (bottomBottom W)) mu)
    (hcross : RectOpNorm2Le (bottomTop W) delta) :
    RectOpNorm2Le (metricGraphOperator W) (mu * delta) := by
  let B : Matrix (Fin k) (Fin k) ℝ := bottomBottom W
  let Binv : Matrix (Fin k) (Fin k) ℝ := squareInverse B
  let C : Matrix (Fin k) (Fin n) ℝ := bottomTop W
  have hBinvT : opNorm2Le (matTranspose Binv) mu :=
    opNorm2Le_transpose Binv hmu0 (by simpa [Binv, B] using hBinv)
  intro x
  have haction :
      rectMatMulVec (metricGraphOperator W) x =
        fun i => -matMulVec k (matTranspose Binv) (rectMatMulVec C x) i := by
    calc
      rectMatMulVec (metricGraphOperator W) x =
          (metricGraphOperator W).mulVec x := by
        rfl
      _ = ((-Binv.transpose) * C).mulVec x := by
        simp [metricGraphOperator, B, Binv, C, squareInverse]
      _ = (-Binv.transpose).mulVec (C.mulVec x) := by
        exact (Matrix.mulVec_mulVec x (-Binv.transpose) C).symm
      _ = fun i =>
          -matMulVec k (matTranspose Binv) (rectMatMulVec C x) i := by
        ext i
        simp [Matrix.mulVec, dotProduct, matMulVec, matTranspose,
          rectMatMulVec, Finset.sum_neg_distrib]
  rw [haction, vecNorm2_neg]
  calc
    vecNorm2 (matMulVec k (matTranspose Binv) (rectMatMulVec C x)) ≤
        mu * vecNorm2 (rectMatMulVec C x) := hBinvT _
    _ ≤ mu * (delta * vecNorm2 x) :=
      mul_le_mul_of_nonneg_left (by simpa [C] using hcross x) hmu0
    _ = (mu * delta) * vecNorm2 x := by ring

/-- Honest nonbreakdown/near-identity certificate needed by the rectangular
inverse-transpose absorption.  Its fields concern only inverses and vector
actions of the explicit matrices generated by `Q` and `D`; it contains no
least-squares minimizer or normal-equation conclusion. -/
structure MetricGraphSmallness (fp : FPModel) {n k : ℕ}
    (Q D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ) : Prop where
  transform_unit : IsUnit (rhsTransformMatrix Q D).det
  bottom_metric_unit :
    IsUnit
      (bottomBottom
        (inverseMetric (squareInverse (rhsTransformMatrix Q D)))).det
  inverse_action :
    opNorm2Le (squareInverse (rhsTransformMatrix Q D))
      (inverseEnvelope fp (n + k) n)
  inverse_difference_action :
    opNorm2Le
      (fun i j => squareInverse (rhsTransformMatrix Q D) i j - Q i j)
      (inverseDifferenceEnvelope fp (n + k) n)
  graph_action :
    RectOpNorm2Le
      (metricGraphOperator
        (inverseMetric (squareInverse (rhsTransformMatrix Q D))))
      (graphEnvelope fp (n + k) n)

/-- The metric-graph certificate is not an independent hypothesis: the
Frobenius RHS-transform perturbation bound and the two explicit scalar
smallness inequalities imply every field. -/
theorem metricGraphSmallness_of_frobNorm_le
    (fp : FPModel) {n k : ℕ}
    (Q D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hD : frobNorm D ≤ rhsRadius fp (n + k) n)
    (hrho : rhsRadius fp (n + k) n < 1)
    (hdelta : metricDefectEnvelope fp (n + k) n < 1) :
    MetricGraphSmallness fp Q D := by
  let rho : ℝ := rhsRadius fp (n + k) n
  let nu : ℝ := inverseEnvelope fp (n + k) n
  let xi : ℝ := inverseDifferenceEnvelope fp (n + k) n
  let delta : ℝ := metricDefectEnvelope fp (n + k) n
  let mu : ℝ := 1 / (1 - delta)
  let P : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := rhsTransformMatrix Q D
  let N : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := squareInverse P
  let W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := inverseMetric N
  have hrho0 : 0 ≤ rho :=
    le_trans (frobNorm_nonneg D) (by simpa [rho] using hD)
  have hden : 0 < 1 - rho := sub_pos.mpr (by simpa [rho] using hrho)
  have hnu0 : 0 ≤ nu := by
    dsimp [nu, inverseEnvelope]
    exact inv_nonneg.mpr hden.le
  have hxi0 : 0 ≤ xi := by
    dsimp [xi, inverseDifferenceEnvelope]
    exact div_nonneg hrho0 hden.le
  obtain ⟨hPunit, hN, hE⟩ :=
    rhsTransform_unit_inverse_and_difference_actions fp Q D hQ hD hrho
  have hdefCoeff : xi * nu + xi = delta := by
    dsimp [xi, nu, delta, inverseDifferenceEnvelope, inverseEnvelope,
      metricDefectEnvelope]
    field_simp [ne_of_gt hden]
    ring
  have hWdefRaw :
      opNorm2Le
        (fun i j => inverseMetric N i j - idMatrix (n + k) i j)
        (xi * nu + xi) :=
    inverseMetric_defect_action_of_inverse_actions N Q hQ hxi0
      (by simpa [N, P, nu] using hN)
      (by simpa [N, P, xi] using hE)
  have hWdef :
      opNorm2Le (fun i j => W i j - idMatrix (n + k) i j) delta := by
    rw [← hdefCoeff]
    simpa [W] using hWdefRaw
  have hbottomDef :
      opNorm2Le
        (fun i j => bottomBottom W i j - idMatrix k i j) delta :=
    bottomBottom_defect_action_of_full_defect_action W hWdef
  obtain ⟨hbottomUnit, hbottomInv⟩ :=
    identity_perturbation_unit_and_inverse_action
      (bottomBottom W) hbottomDef (by simpa [delta] using hdelta)
  have hcross : RectOpNorm2Le (bottomTop W) delta :=
    bottomTop_action_of_full_defect_action W hWdef
  have hdelta0 : 0 ≤ delta := by
    rw [← hdefCoeff]
    exact add_nonneg (mul_nonneg hxi0 hnu0) hxi0
  have hmu0 : 0 ≤ mu := by
    dsimp [mu]
    exact (one_div_pos.mpr
      (sub_pos.mpr (by simpa [delta] using hdelta))).le
  have hgraphRaw :
      RectOpNorm2Le (metricGraphOperator W) (mu * delta) :=
    metricGraphOperator_action_of_block_actions W hmu0
      (by simpa [mu] using hbottomInv) hcross
  have hgraphCoeff : mu * delta = graphEnvelope fp (n + k) n := by
    dsimp [mu, delta, graphEnvelope]
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [P] using hPunit
  · simpa [W, N, P] using hbottomUnit
  · simpa [N, P, nu] using hN
  · simpa [N, P, xi] using hE
  · rw [← hgraphCoeff]
    simpa [W, N, P] using hgraphRaw

/-- Dimension-only coefficient delivered once the near-identity inverse and
metric-graph guards have been discharged. -/
noncomputable def matrixOnlyCoeff (fp : FPModel) (m n : ℕ) : ℝ :=
  let η := H19.Theorem19_4.gamma_tilde fp m n
  let g := gamma fp n
  η + (1 + η) *
    (inverseDifferenceEnvelope fp m n +
      inverseEnvelope fp m n *
        (g + graphEnvelope fp m n * (1 + g)))

/-- One coefficient covering the nonzero-RHS metric-graph construction and
the exact zero-RHS branch inherited from Theorem 20.3. -/
noncomputable def matrixOnlyCombinedCoeff (fp : FPModel) (m n : ℕ) : ℝ :=
  max (matrixOnlyCoeff fp m n) (Theorem20_3.gamma_tilde_mn fp m n)

theorem orthogonal_mul_transpose_rect {m n : ℕ}
    (Q : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (hQ : IsOrthogonal m Q) :
    matMulRectLeft Q (matMulRectLeft (matTranspose Q) B) = B := by
  have hQQt : matMul m Q (matTranspose Q) = idMatrix m := by
    simpa [matMul, finiteMatMul, idMatrix, finiteIdMatrix] using
      finiteMatMul_self_matTranspose_of_isOrthogonal hQ
  rw [← matMulRectLeft_assoc, hQQt, matMulRectLeft_id]

theorem column_norm_of_transformed_orthogonal {m n : ℕ}
    (Q : Matrix (Fin m) (Fin m) ℝ) (B R : Matrix (Fin m) (Fin n) ℝ)
    (hQ : IsOrthogonal m Q)
    (hR : ∀ i j, R i j = matMulRectLeft (matTranspose Q) B i j)
    (j : Fin n) :
    vecNorm2 (fun i : Fin m => R i j) = vecNorm2 (fun i : Fin m => B i j) := by
  have hcol : (fun i : Fin m => R i j) =
      matMulVec m (matTranspose Q) (fun i : Fin m => B i j) := by
    funext i
    simpa [matMulVec, matMulRectLeft] using hR i j
  rw [hcol]
  exact vecNorm2_orthogonal (matTranspose Q) (fun i : Fin m => B i j) hQ.transpose

/-- The matrix obtained by absorbing a transformed-RHS error into the QR
matrix and adding the rectangular metric-graph correction. -/
noncomputable def absorbedMatrix {n k : ℕ}
    (P : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + k)) (Fin n) ℝ :=
  let N := squareInverse P
  let W := inverseMetric N
  N * stack T (metricGraphBottom W T)

/-- Quantitative rectangular absorption assembly.  All algorithmic error
inputs have the standard QR and back-substitution forms.  The only additional
hypothesis is `MetricGraphSmallness`, which is the explicit near-identity
inverse certificate isolated above. -/
theorem absorbedMatrix_columnwise_bound
    (fp : FPModel) {n k : ℕ}
    (A E : Matrix (Fin (n + k)) (Fin n) ℝ)
    (Q D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (R F : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hR : ∀ i j,
      stack R (0 : Matrix (Fin k) (Fin n) ℝ) i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + E a b) i j)
    (hE : ∀ j : Fin n,
      vecNorm2 (fun i : Fin (n + k) => E i j) ≤
        H19.Theorem19_4.gamma_tilde fp (n + k) n *
          vecNorm2 (fun i : Fin (n + k) => A i j))
    (hF : ∀ i j, |F i j| ≤ gamma fp n * |R i j|)
    (hvalid : gammaValid fp n)
    (hvalidQR :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + k)))
    (hν0 : 0 ≤ inverseEnvelope fp (n + k) n)
    (hξ0 : 0 ≤ inverseDifferenceEnvelope fp (n + k) n)
    (hlam0 : 0 ≤ graphEnvelope fp (n + k) n)
    (hmetric : MetricGraphSmallness fp Q D) :
    ∀ j : Fin n,
      vecNorm2 (fun i : Fin (n + k) =>
        absorbedMatrix (rhsTransformMatrix Q D)
            (fun a b => R a b + F a b) i j - A i j) ≤
        matrixOnlyCoeff fp (n + k) n *
          vecNorm2 (fun i : Fin (n + k) => A i j) := by
  intro j
  let η : ℝ := H19.Theorem19_4.gamma_tilde fp (n + k) n
  let g : ℝ := gamma fp n
  let ν : ℝ := inverseEnvelope fp (n + k) n
  let ξ : ℝ := inverseDifferenceEnvelope fp (n + k) n
  let lam : ℝ := graphEnvelope fp (n + k) n
  let P : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := rhsTransformMatrix Q D
  let N : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := squareInverse P
  let W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := inverseMetric N
  let G : Matrix (Fin k) (Fin n) ℝ := metricGraphOperator W
  let T : Matrix (Fin n) (Fin n) ℝ := fun a b => R a b + F a b
  let L : Matrix (Fin k) (Fin n) ℝ := G * T
  let S : Matrix (Fin (n + k)) (Fin n) ℝ := stack T L
  let Rbar : Matrix (Fin (n + k)) (Fin n) ℝ :=
    stack R (0 : Matrix (Fin k) (Fin n) ℝ)
  let C : Matrix (Fin (n + k)) (Fin n) ℝ := N * S
  let aNorm : ℝ := vecNorm2 (fun i : Fin (n + k) => A i j)
  let rNorm : ℝ := vecNorm2 (fun i : Fin (n + k) => Rbar i j)
  have hg0 : 0 ≤ g := gamma_nonneg fp hvalid
  have ha0 : 0 ≤ aNorm := vecNorm2_nonneg _
  have hη0 : 0 ≤ η := by
    exact H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hRcol :
      vecNorm2 (fun i : Fin n => R i j) = rNorm := by
    have happ : (fun i : Fin (n + k) => Rbar i j) =
        Fin.append (fun i : Fin n => R i j) (0 : Fin k → ℝ) := by
      funext i
      refine Fin.addCases (motive := fun i : Fin (n + k) =>
        Rbar i j = Fin.append (fun i : Fin n => R i j) (0 : Fin k → ℝ) i)
        ?_ ?_ i
      · intro i
        simp [Rbar, stack_top, Fin.append_left]
      · intro i
        simp [Rbar, stack_bottom, Fin.append_right]
    dsimp [rNorm]
    rw [happ]
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  have hRnorm_eq :
      rNorm = vecNorm2 (fun i : Fin (n + k) => A i j + E i j) := by
    dsimp [rNorm, Rbar]
    exact column_norm_of_transformed_orthogonal Q
      (fun a b => A a b + E a b)
      (stack R (0 : Matrix (Fin k) (Fin n) ℝ)) hQ hR j
  have hr_le : rNorm ≤ (1 + η) * aNorm := by
    calc
      rNorm = vecNorm2 (fun i : Fin (n + k) => A i j + E i j) := hRnorm_eq
      _ ≤ aNorm + vecNorm2 (fun i : Fin (n + k) => E i j) :=
        vecNorm2_add_le _ _
      _ ≤ aNorm + η * aNorm := by
        exact add_le_add le_rfl (by simpa [η, aNorm] using hE j)
      _ = (1 + η) * aNorm := by ring
  have hFcol : vecNorm2 (fun i : Fin n => F i j) ≤ g * rNorm := by
    have hentry : ∀ i : Fin n, |F i j| ≤ (fun i : Fin n => g * |R i j|) i := by
      intro i
      simpa [g] using hF i j
    calc
      vecNorm2 (fun i : Fin n => F i j)
          ≤ vecNorm2 (fun i : Fin n => g * |R i j|) :=
            vecNorm2_le_of_abs_le _ _ hentry
      _ = g * vecNorm2 (fun i : Fin n => R i j) := by
        have habs : (fun i : Fin n => |R i j|) = fun i : Fin n => abs (R i j) := rfl
        rw [vecNorm2_smul, abs_of_nonneg hg0]
        congr 1
        exact vecNorm2_abs (fun i : Fin n => R i j)
      _ = g * rNorm := by rw [hRcol]
  have hTcol : vecNorm2 (fun i : Fin n => T i j) ≤ (1 + g) * rNorm := by
    calc
      vecNorm2 (fun i : Fin n => T i j)
          ≤ vecNorm2 (fun i : Fin n => R i j) +
              vecNorm2 (fun i : Fin n => F i j) := by
            dsimp [T]
            exact vecNorm2_add_le _ _
      _ ≤ rNorm + g * rNorm := by rw [hRcol]; gcongr
      _ = (1 + g) * rNorm := by ring
  have hLcol : vecNorm2 (fun i : Fin k => L i j) ≤ lam * (1 + g) * rNorm := by
    have hGT : (fun i : Fin k => L i j) =
        rectMatMulVec G (fun i : Fin n => T i j) := by
      funext i
      rfl
    rw [hGT]
    calc
      vecNorm2 (rectMatMulVec G (fun i : Fin n => T i j))
          ≤ lam * vecNorm2 (fun i : Fin n => T i j) := by
            simpa [G, W, N, P, lam] using
              hmetric.graph_action (fun i : Fin n => T i j)
      _ ≤ lam * ((1 + g) * rNorm) := by
            exact mul_le_mul_of_nonneg_left hTcol (by simpa [lam] using hlam0)
      _ = lam * (1 + g) * rNorm := by ring
  have hdiff :
      vecNorm2 (fun i : Fin (n + k) => S i j - Rbar i j) ≤
        (g + lam * (1 + g)) * rNorm := by
    have happend : (fun i : Fin (n + k) => S i j - Rbar i j) =
        Fin.append (fun i : Fin n => F i j) (fun i : Fin k => L i j) := by
      funext i
      refine Fin.addCases (motive := fun i : Fin (n + k) =>
        S i j - Rbar i j =
          Fin.append (fun i : Fin n => F i j) (fun i : Fin k => L i j) i)
        ?_ ?_ i
      · intro i
        simp [S, Rbar, T, stack_top, Fin.append_left]
      · intro i
        simp [S, Rbar, stack_bottom, Fin.append_right]
    rw [happend]
    calc
      vecNorm2 (Fin.append (fun i : Fin n => F i j) (fun i : Fin k => L i j))
          ≤ vecNorm2 (fun i : Fin n => F i j) +
              vecNorm2 (fun i : Fin k => L i j) :=
            lsVecNorm2_append_le_add _ _
      _ ≤ g * rNorm + lam * (1 + g) * rNorm := add_le_add hFcol hLcol
      _ = (g + lam * (1 + g)) * rNorm := by ring
  have hNR :
      vecNorm2 (rectMatMulVec
          (fun i l => N i l - Q i l) (fun i : Fin (n + k) => Rbar i j)) ≤
        ξ * rNorm := by
    simpa [N, P, ξ, rNorm, matMulVec, rectMatMulVec] using
      hmetric.inverse_difference_action (fun i : Fin (n + k) => Rbar i j)
  have hNdiff :
      vecNorm2 (rectMatMulVec N (fun i : Fin (n + k) => S i j - Rbar i j)) ≤
        ν * ((g + lam * (1 + g)) * rNorm) := by
    calc
      vecNorm2 (rectMatMulVec N (fun i : Fin (n + k) => S i j - Rbar i j))
          ≤ ν * vecNorm2 (fun i : Fin (n + k) => S i j - Rbar i j) := by
            have hh := hmetric.inverse_action
              (fun i : Fin (n + k) => S i j - Rbar i j)
            change vecNorm2
                (rectMatMulVec (squareInverse (rhsTransformMatrix Q D))
                  (fun i : Fin (n + k) => S i j - Rbar i j)) ≤
              inverseEnvelope fp (n + k) n *
                vecNorm2 (fun i : Fin (n + k) => S i j - Rbar i j) at hh
            simpa [N, P, ν] using hh
      _ ≤ ν * ((g + lam * (1 + g)) * rNorm) :=
        mul_le_mul_of_nonneg_left hdiff (by simpa [ν] using hν0)
  have hCQR :
      vecNorm2 (fun i : Fin (n + k) =>
        C i j - matMulRectLeft Q Rbar i j) ≤
        (ξ + ν * (g + lam * (1 + g))) * rNorm := by
    have hsplit : (fun i : Fin (n + k) =>
        C i j - matMulRectLeft Q Rbar i j) =
      fun i =>
        rectMatMulVec (fun a l => N a l - Q a l)
            (fun l : Fin (n + k) => Rbar l j) i +
          rectMatMulVec N (fun l : Fin (n + k) => S l j - Rbar l j) i := by
      funext i
      dsimp [C]
      rw [Matrix.mul_apply]
      unfold rectMatMulVec matMulRectLeft
      simp_rw [sub_mul, mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    calc
      vecNorm2 (fun i : Fin (n + k) =>
          rectMatMulVec (fun a l => N a l - Q a l)
              (fun l : Fin (n + k) => Rbar l j) i +
            rectMatMulVec N (fun l : Fin (n + k) => S l j - Rbar l j) i)
          ≤ vecNorm2 (rectMatMulVec (fun a l => N a l - Q a l)
                (fun l : Fin (n + k) => Rbar l j)) +
              vecNorm2 (rectMatMulVec N
                (fun l : Fin (n + k) => S l j - Rbar l j)) :=
            vecNorm2_add_le _ _
      _ ≤ ξ * rNorm + ν * ((g + lam * (1 + g)) * rNorm) :=
        add_le_add hNR hNdiff
      _ = (ξ + ν * (g + lam * (1 + g))) * rNorm := by ring
  have hQR : matMulRectLeft Q Rbar = fun i j => A i j + E i j := by
    have hRt : Rbar =
        matMulRectLeft (matTranspose Q) (fun i j => A i j + E i j) := by
      funext i j
      exact hR i j
    rw [hRt]
    exact orthogonal_mul_transpose_rect Q (fun i j => A i j + E i j) hQ
  have hfinal :
      vecNorm2 (fun i : Fin (n + k) => C i j - A i j) ≤
        η * aNorm +
          (ξ + ν * (g + lam * (1 + g))) * ((1 + η) * aNorm) := by
    have hsplit : (fun i : Fin (n + k) => C i j - A i j) =
        fun i => (C i j - matMulRectLeft Q Rbar i j) + E i j := by
      funext i
      have hi := congrArg (fun M : Matrix (Fin (n + k)) (Fin n) ℝ => M i j) hQR
      linarith
    rw [hsplit]
    calc
      vecNorm2 (fun i : Fin (n + k) =>
          (C i j - matMulRectLeft Q Rbar i j) + E i j)
          ≤ vecNorm2 (fun i : Fin (n + k) =>
              C i j - matMulRectLeft Q Rbar i j) +
              vecNorm2 (fun i : Fin (n + k) => E i j) :=
            vecNorm2_add_le _ _
      _ ≤ (ξ + ν * (g + lam * (1 + g))) * rNorm + η * aNorm :=
        add_le_add hCQR (by simpa [η, aNorm] using hE j)
      _ ≤ (ξ + ν * (g + lam * (1 + g))) * ((1 + η) * aNorm) +
          η * aNorm := by
            have hcoef0 : 0 ≤ ξ + ν * (g + lam * (1 + g)) := by
              have h1g : 0 ≤ 1 + g := by linarith
              have hinner : 0 ≤ g + lam * (1 + g) := by
                exact add_nonneg hg0 (mul_nonneg (by simpa [lam] using hlam0) h1g)
              exact add_nonneg (by simpa [ξ] using hξ0)
                (mul_nonneg (by simpa [ν] using hν0) hinner)
            linarith [mul_le_mul_of_nonneg_left hr_le hcoef0]
      _ = η * aNorm +
          (ξ + ν * (g + lam * (1 + g))) * ((1 + η) * aNorm) := by ring
  have hcoeff :
      η * aNorm +
          (ξ + ν * (g + lam * (1 + g))) * ((1 + η) * aNorm) =
        matrixOnlyCoeff fp (n + k) n * aNorm := by
    simp [matrixOnlyCoeff, η, g, ν, ξ, lam]
    ring
  have hCeq : absorbedMatrix P T = C := by
    simp [absorbedMatrix, C, S, L, T, G, W, N, P,
      metricGraphBottom_eq_operator_mul]
  simpa [P, T, C, aNorm, hCeq] using hfinal.trans_eq hcoeff

/-- The defining graph equation.  It is stated in the orientation used by the
normal equations: the transpose of the bottom graph cancels the top-to-bottom
metric block. -/
theorem metricGraphBottom_transpose_mul_bottomBottom {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hWsymm : W.transpose = W)
    (hunit : IsUnit (bottomBottom W).det) :
    (metricGraphBottom W T).transpose * bottomBottom W =
      -(T.transpose * topBottom W) := by
  have hblocks : (bottomTop W).transpose = topBottom W := by
    ext i j
    have hij := congrArg (fun M => M (Fin.castAdd k i) (Fin.natAdd n j)) hWsymm
    simpa [bottomTop, topBottom] using hij
  have hinv : (bottomBottom W)⁻¹ * bottomBottom W = 1 :=
    Matrix.nonsing_inv_mul (bottomBottom W) hunit
  simp only [metricGraphBottom, Matrix.transpose_mul, Matrix.transpose_neg,
    Matrix.transpose_transpose]
  rw [hblocks]
  calc
    T.transpose * (topBottom W * -(bottomBottom W)⁻¹) * bottomBottom W
        = -(T.transpose * topBottom W *
            ((bottomBottom W)⁻¹ * bottomBottom W)) := by
              simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(T.transpose * topBottom W) := by simp [hinv]

/-- The graph columns are `W`-orthogonal to every bottom coordinate vector. -/
theorem stack_metricGraph_mul_metric_bottom_entry_eq_zero {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hWsymm : W.transpose = W)
    (hunit : IsUnit (bottomBottom W).det)
    (j : Fin n) (q : Fin k) :
    ((stack T (metricGraphBottom W T)).transpose * W)
        j (Fin.natAdd n q) = 0 := by
  have hgraph :=
    metricGraphBottom_transpose_mul_bottomBottom W T hWsymm hunit
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin k) ℝ => M j q) hgraph
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have htop :
      (∑ i : Fin n,
          (stack T (metricGraphBottom W T)).transpose j (Fin.castAdd k i) *
            W (Fin.castAdd k i) (Fin.natAdd n q)) =
        (T.transpose * topBottom W) j q := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, stack_top, topBottom]
  have hbottom :
      (∑ i : Fin k,
          (stack T (metricGraphBottom W T)).transpose j (Fin.natAdd n i) *
            W (Fin.natAdd n i) (Fin.natAdd n q)) =
        ((metricGraphBottom W T).transpose * bottomBottom W) j q := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, stack_bottom, bottomBottom]
  rw [htop, hbottom]
  have hentry' :
      ((metricGraphBottom W T).transpose * bottomBottom W) j q =
        -(T.transpose * topBottom W) j q := by
    simpa using hentry
  rw [hentry']
  ring

/-- Vector form of the graph orthogonality lemma. -/
theorem stack_metricGraph_mul_metric_mulVec_eq_zero_of_top_zero {n k : ℕ}
    (W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hWsymm : W.transpose = W)
    (hunit : IsUnit (bottomBottom W).det)
    (z : Fin (n + k) → ℝ)
    (hz : ∀ i : Fin n, z (Fin.castAdd k i) = 0) :
    ((stack T (metricGraphBottom W T)).transpose * W).mulVec z = 0 := by
  funext j
  change (∑ i : Fin (n + k),
    ((stack T (metricGraphBottom W T)).transpose * W) j i * z i) = 0
  rw [Fin.sum_univ_add]
  have htop :
      (∑ i : Fin n,
          ((stack T (metricGraphBottom W T)).transpose * W)
              j (Fin.castAdd k i) * z (Fin.castAdd k i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i]
    ring
  have hbottom :
      (∑ i : Fin k,
          ((stack T (metricGraphBottom W T)).transpose * W)
              j (Fin.natAdd n i) * z (Fin.natAdd n i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [stack_metricGraph_mul_metric_bottom_entry_eq_zero
      W T hWsymm hunit j i]
    ring
  rw [htop, hbottom]
  ring

/-- Exact rectangular inverse-transpose/metric-graph absorption theorem.

`c = P b` is the computed transformed right-hand side and `T x = c_top` is
the (possibly backward-perturbed) triangular solve.  Provided `P` and the
bottom metric block are nonsingular, the literal vector `x` is an exact least
squares minimizer for the *unperturbed* right-hand side `b` and the explicitly
constructed matrix `absorbedMatrix P T`.

This theorem contains no minimizer or normal-equation premise. -/
theorem absorbedMatrix_isLeastSquaresMinimizer {n k : ℕ}
    (P : Matrix (Fin (n + k)) (Fin (n + k)) ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin (n + k) → ℝ) (x : Fin n → ℝ)
    (hPunit : IsUnit P.det)
    (hWunit : IsUnit (bottomBottom (inverseMetric (P⁻¹))).det)
    (hc : c = P.mulVec b)
    (hx : T.mulVec x = fun i : Fin n => c (Fin.castAdd k i)) :
    IsLeastSquaresMinimizer (absorbedMatrix P T) b x := by
  let N : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := squareInverse P
  let W : Matrix (Fin (n + k)) (Fin (n + k)) ℝ := inverseMetric N
  let L : Matrix (Fin k) (Fin n) ℝ := metricGraphBottom W T
  let S : Matrix (Fin (n + k)) (Fin n) ℝ := stack T L
  let C : Matrix (Fin (n + k)) (Fin n) ℝ := N * S
  let z : Fin (n + k) → ℝ := c - S.mulVec x
  have hNP : N * P = 1 := by
    dsimp [N]
    exact Matrix.nonsing_inv_mul P hPunit
  have hNb : N.mulVec c = b := by
    rw [hc]
    rw [Matrix.mulVec_mulVec]
    rw [hNP]
    simp
  have hz_top : ∀ i : Fin n, z (Fin.castAdd k i) = 0 := by
    intro i
    dsimp [z]
    change c (Fin.castAdd k i) -
      (∑ j : Fin n, S (Fin.castAdd k i) j * x j) = 0
    have hS : S (Fin.castAdd k i) = T i := by
      funext j
      simp [S, L, stack_top]
    have hxi := congrFun hx i
    change (∑ j : Fin n, T i j * x j) = c (Fin.castAdd k i) at hxi
    rw [hS, hxi]
    ring
  have hWsymm : W.transpose = W := by
    dsimp [W]
    exact inverseMetric_symmetric N
  have hgraph : (S.transpose * W).mulVec z = 0 := by
    dsimp [S, L]
    exact stack_metricGraph_mul_metric_mulVec_eq_zero_of_top_zero
      W T hWsymm (by simpa [W, N] using hWunit) z hz_top
  have hres : lsResidualHigham C b x = N.mulVec z := by
    funext i
    have hCS : C.mulVec x = N.mulVec (S.mulVec x) := by
      rw [Matrix.mulVec_mulVec]
    have hNsub : N.mulVec z = N.mulVec c - N.mulVec (S.mulVec x) := by
      dsimp [z]
      exact Matrix.mulVec_sub N c (S.mulVec x)
    change b i - C.mulVec x i = N.mulVec z i
    rw [hCS, hNsub, hNb]
    rfl
  have hnormal : C.transpose.mulVec (lsResidualHigham C b x) = 0 := by
    rw [hres]
    rw [Matrix.mulVec_mulVec]
    have hCtN : C.transpose * N = S.transpose * W := by
      dsimp [C, W, inverseMetric]
      rw [Matrix.transpose_mul]
      rw [Matrix.mul_assoc]
    rw [hCtN]
    exact hgraph
  have hrect : RectLSNormalEquations C b x := by
    apply RectLSNormalEquations.of_residual_orthogonal
    intro j
    have hj := congrFun hnormal j
    change (∑ i : Fin (n + k), C i j * lsResidualHigham C b x i) = 0 at hj
    rw [lsResidualHigham_eq_neg_lsResidual C b x] at hj
    simp only [mul_neg, Finset.sum_neg_distrib] at hj
    linarith
  have hmin : IsLeastSquaresMinimizer C b x := hrect.isLeastSquaresMinimizer
  simpa [absorbedMatrix, C, S, L, W, N] using hmin

/-- Source-facing p. 385 `Δb = 0` theorem for the repository's literal
Householder-QR plus `fl_backSub` implementation, in dimensions `m = n+k`.

The standard floating-point QR, RHS-transform, and triangular-solve
certificates are all derived internally.  The explicit remaining guards are
only the nonbreakdown/Neumann bounds for the inverse-transpose metric graph;
they are collected in `MetricGraphSmallness` and contain no target-equivalent
least-squares hypothesis. -/
theorem householder_qr_fl_backSub_matrix_only_backward_error
    (fp : FPModel) {n k : ℕ}
    (A : Matrix (Fin (n + k)) (Fin n) ℝ)
    (b : Fin (n + k) → ℝ)
    (hn : 0 < n) (hb : b ≠ 0)
    (hvalid : gammaValid fp (Theorem20_3.gammaIndex (n + k) n))
    (hdiag : ∀ i : Fin n,
      Theorem20_3.computedR fp A (Nat.le_add_right n k) i i ≠ 0)
    (hν0 : 0 ≤ inverseEnvelope fp (n + k) n)
    (hξ0 : 0 ≤ inverseDifferenceEnvelope fp (n + k) n)
    (hlam0 : 0 ≤ graphEnvelope fp (n + k) n)
    (hmetric : ∀ D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ,
      frobNorm D ≤ rhsRadius fp (n + k) n →
        MetricGraphSmallness fp
          (fl_householderQRPanel_Q fp (n + k) n A) D) :
    ∃ ΔA : Matrix (Fin (n + k)) (Fin n) ℝ,
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin (n + k) => ΔA i j) ≤
          matrixOnlyCoeff fp (n + k) n *
            vecNorm2 (fun i : Fin (n + k) => A i j)) ∧
      IsLeastSquaresMinimizer (fun i j => A i j + ΔA i j) b
        (Theorem20_3.computedX fp A b (Nat.le_add_right n k)) := by
  let m : ℕ := n + k
  let hmn : n ≤ m := Nat.le_add_right n k
  let Q : Matrix (Fin m) (Fin m) ℝ := fl_householderQRPanel_Q fp m n A
  let R : Matrix (Fin n) (Fin n) ℝ := Theorem20_3.computedR fp A hmn
  let cfull : Fin m → ℝ := fl_householderQRPanel_rhs fp m n A b
  let ctop : Fin n → ℝ := Theorem20_3.computedC fp A b hmn
  let xhat : Fin n → ℝ := Theorem20_3.computedX fp A b hmn
  have hvalid_n : gammaValid fp n :=
    gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid
  have hvalid_qr :
      gammaValid fp (n * householderConstructApplyGammaIndex m) :=
    by
      simpa [m] using
        (gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid :
          gammaValid fp
            (n * householderConstructApplyGammaIndex (n + k)))
  have hvalid_base : gammaValid fp (11 * m + 23) :=
    by
      simpa [m] using
        (gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid :
          gammaValid fp (11 * (n + k) + 23))
  have hvalid_rhs :
      gammaValid fp (householderQRRhsPanelGammaClosedGrowthIndex m n) :=
    by
      simpa [m] using
        (gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid :
          gammaValid fp
            (householderQRRhsPanelGammaClosedGrowthIndex (n + k) n))
  have hsteps : 0 < Nat.min m n := by
    simpa [m, Nat.min_eq_right hmn] using hn
  have hpanel :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp m n A hsteps (by simpa [Nat.min_eq_right hmn] using hvalid_qr)
  rcases hpanel.result with ⟨E, hAhat, _hE_frob, hEcols⟩
  have hready : HouseholderQRPanelReady fp m n A :=
    HouseholderQRPanelReady_of_global_gammaValid fp m n m A le_rfl hvalid_base
  rcases fl_householderQRPanel_rhs_explicit_vecNorm2_perturbation_bound
      fp m n A b hready with ⟨db, hc_fixedQ, hdb_raw⟩
  have hraw_le_inf :
      householderQRRhsPanelBackwardBound fp m n A b ≤
        gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
          infNormVec b :=
    householderQRRhsPanelBackwardBound_le_gammaClosedGrowthIndex
      fp m n A b hmn hvalid_rhs hready
  have hinf_le_vec : infNormVec b ≤ vecNorm2 b :=
    infNormVec_le_of_abs_le b
      (fun i => abs_coord_le_vecNorm2 b i) (vecNorm2_nonneg b)
  have hgamma_rhs_nonneg :
      0 ≤ gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) :=
    gamma_nonneg fp hvalid_rhs
  have hsqrt_nonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hdb : vecNorm2 db ≤ rhsRadius fp m n * vecNorm2 b := by
    calc
      vecNorm2 db
          ≤ Real.sqrt (m : ℝ) *
              householderQRRhsPanelBackwardBound fp m n A b := hdb_raw
      _ ≤ Real.sqrt (m : ℝ) *
            (gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
              infNormVec b) :=
          mul_le_mul_of_nonneg_left hraw_le_inf hsqrt_nonneg
      _ ≤ Real.sqrt (m : ℝ) *
            (gamma fp (householderQRRhsPanelGammaClosedGrowthIndex m n) *
              vecNorm2 b) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinf_le_vec hgamma_rhs_nonneg)
            hsqrt_nonneg
      _ = rhsRadius fp m n * vecNorm2 b := by
          simp [rhsRadius, Theorem20_3.rhsCoeff, mul_assoc]
  have hc_fixedQ' : ∀ i, cfull i =
      matMulVec m (fun p q => Q q p) (fun j => b j + db j) i := by
    intro i
    simpa [cfull, Q, matTranspose, matMulRectLeft] using hc_fixedQ i
  rcases H19_Lemma19_3_vector_QplusDeltaQ_form
      Q hpanel.orth b cfull db hb hc_fixedQ' hdb with
    ⟨D, hcD, hDnorm⟩
  have hmD : MetricGraphSmallness fp Q D := by
    apply hmetric
    simpa [m, Q, rhsRadius] using hDnorm
  have hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    intro i j hji
    exact hpanel.upper
      ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji
  rcases backSub_backward_error fp n R ctop hdiag hupper hvalid_n with
    ⟨F, hF, hxF⟩
  let T : Matrix (Fin n) (Fin n) ℝ := fun i j => R i j + F i j
  let P : Matrix (Fin m) (Fin m) ℝ := rhsTransformMatrix Q D
  have hcP : cfull = P.mulVec b := by
    funext i
    change cfull i = ∑ j : Fin m, P i j * b j
    simpa [P, rhsTransformMatrix, matMulVec] using hcD i
  have hctop : ∀ i : Fin n, ctop i = cfull (Fin.castAdd k i) := by
    intro i
    rfl
  have hxT : T.mulVec xhat = fun i : Fin n => cfull (Fin.castAdd k i) := by
    funext i
    change (∑ j : Fin n, (R i j + F i j) * xhat j) =
      cfull (Fin.castAdd k i)
    rw [← hctop i]
    simpa [xhat, Theorem20_3.computedX, T] using hxF i
  have hminC : IsLeastSquaresMinimizer (absorbedMatrix P T) b xhat :=
    absorbedMatrix_isLeastSquaresMinimizer P T b cfull xhat
      hmD.transform_unit hmD.bottom_metric_unit hcP hxT
  have hRstack : ∀ i j,
      stack R (0 : Matrix (Fin k) (Fin n) ℝ) i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + E a b) i j := by
    intro i j
    calc
      stack R (0 : Matrix (Fin k) (Fin n) ℝ) i j =
          fl_householderQRPanel_R fp m n A i j := by
        refine Fin.addCases
          (motive := fun i : Fin (n + k) =>
            stack R (0 : Matrix (Fin k) (Fin n) ℝ) i j =
              fl_householderQRPanel_R fp m n A i j) ?_ ?_ i
        · intro r
          rw [stack_top]
          dsimp [R, Theorem20_3.computedR]
          congr 2
        · intro r
          rw [stack_bottom]
          symm
          exact hpanel.upper (Fin.natAdd n r) j (by
            simp [Fin.natAdd]
            omega)
      _ = matMulRectLeft (matTranspose Q)
          (fun a b => A a b + E a b) i j := by
        simpa [matMulRectLeft, matMulRect] using hAhat i j
  have hEcols' : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => E i j) ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          vecNorm2 (fun i : Fin m => A i j) := by
    intro j
    simpa [H19.Theorem19_4.gamma_tilde, Nat.min_eq_right hmn,
      columnFrob_eq_vecNorm2] using hEcols j
  have hcolC := absorbedMatrix_columnwise_bound fp A E Q D R F hpanel.orth
    hRstack hEcols' hF hvalid_n hvalid_qr
    (by simpa [m] using hν0) (by simpa [m] using hξ0)
    (by simpa [m] using hlam0) hmD
  let ΔA : Matrix (Fin m) (Fin n) ℝ :=
    fun i j => absorbedMatrix P T i j - A i j
  refine ⟨ΔA, ?_, ?_⟩
  · intro j
    simpa [ΔA, m, P, T, Q, R] using hcolC j
  · have hmat : (fun i j => A i j + ΔA i j) = absorbedMatrix P T := by
      funext i j
      simp [ΔA]
    rw [hmat]
    simpa [xhat, m, hmn] using hminC

/-- Full p. 385 matrix-only theorem, including `b = 0`.

For nonzero `b` this is the inverse-transpose metric-graph construction.  For
`b = 0`, the already-proved Theorem 20.3 certificate has
`‖Δb‖₂ ≤ gamma_tilde*‖0‖₂ = 0`, hence `Δb` is identically zero. -/
theorem householder_qr_fl_backSub_matrix_only_backward_error_all_rhs
    (fp : FPModel) {n k : ℕ}
    (A : Matrix (Fin (n + k)) (Fin n) ℝ)
    (b : Fin (n + k) → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp (Theorem20_3.gammaIndex (n + k) n))
    (hdiag : ∀ i : Fin n,
      Theorem20_3.computedR fp A (Nat.le_add_right n k) i i ≠ 0)
    (hν0 : 0 ≤ inverseEnvelope fp (n + k) n)
    (hξ0 : 0 ≤ inverseDifferenceEnvelope fp (n + k) n)
    (hlam0 : 0 ≤ graphEnvelope fp (n + k) n)
    (hmetric : ∀ D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ,
      frobNorm D ≤ rhsRadius fp (n + k) n →
        MetricGraphSmallness fp
          (fl_householderQRPanel_Q fp (n + k) n A) D) :
    ∃ ΔA : Matrix (Fin (n + k)) (Fin n) ℝ,
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin (n + k) => ΔA i j) ≤
          matrixOnlyCombinedCoeff fp (n + k) n *
            vecNorm2 (fun i : Fin (n + k) => A i j)) ∧
      IsLeastSquaresMinimizer (fun i j => A i j + ΔA i j) b
        (Theorem20_3.computedX fp A b (Nat.le_add_right n k)) := by
  by_cases hb : b = 0
  · subst b
    rcases Theorem20_3.householder_qr_fl_backSub_backward_error
        fp A (0 : Fin (n + k) → ℝ) hn (Nat.le_add_right n k)
        hvalid hdiag with ⟨ΔA, db, hA, hdb, hmin⟩
    have hdb0norm : vecNorm2 db = 0 := by
      have hle : vecNorm2 db ≤ 0 := by
        simpa [vecNorm2, vecNorm2Sq] using hdb
      exact le_antisymm hle (vecNorm2_nonneg db)
    have hdb0 : db = 0 := by
      funext i
      exact (vecNorm2_eq_zero_iff db).mp hdb0norm i
    refine ⟨ΔA, ?_, ?_⟩
    · intro j
      exact le_trans (hA j)
        (mul_le_mul_of_nonneg_right
          (le_max_right (matrixOnlyCoeff fp (n + k) n)
            (Theorem20_3.gamma_tilde_mn fp (n + k) n))
          (vecNorm2_nonneg _))
    · simpa [hdb0] using hmin
  · rcases householder_qr_fl_backSub_matrix_only_backward_error
        fp A b hn hb hvalid hdiag hν0 hξ0 hlam0 hmetric with
      ⟨ΔA, hA, hmin⟩
    refine ⟨ΔA, ?_, hmin⟩
    intro j
    exact le_trans (hA j)
      (mul_le_mul_of_nonneg_right
        (le_max_left (matrixOnlyCoeff fp (n + k) n)
          (Theorem20_3.gamma_tilde_mn fp (n + k) n))
        (vecNorm2_nonneg _))

/-- Final p. 385 matrix-only theorem for the actual repository computation.
The former `MetricGraphSmallness` guard has been discharged into the two
displayed scalar Neumann inequalities. -/
theorem householder_qr_fl_backSub_matrix_only_backward_error_all_rhs_of_scalar_smallness
    (fp : FPModel) {n k : ℕ}
    (A : Matrix (Fin (n + k)) (Fin n) ℝ)
    (b : Fin (n + k) → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp (Theorem20_3.gammaIndex (n + k) n))
    (hdiag : ∀ i : Fin n,
      Theorem20_3.computedR fp A (Nat.le_add_right n k) i i ≠ 0)
    (hrho : rhsRadius fp (n + k) n < 1)
    (hdelta : metricDefectEnvelope fp (n + k) n < 1) :
    ∃ ΔA : Matrix (Fin (n + k)) (Fin n) ℝ,
      (∀ j : Fin n,
        vecNorm2 (fun i : Fin (n + k) => ΔA i j) ≤
          matrixOnlyCombinedCoeff fp (n + k) n *
            vecNorm2 (fun i : Fin (n + k) => A i j)) ∧
      IsLeastSquaresMinimizer (fun i j => A i j + ΔA i j) b
        (Theorem20_3.computedX fp A b (Nat.le_add_right n k)) := by
  let rho : ℝ := rhsRadius fp (n + k) n
  let delta : ℝ := metricDefectEnvelope fp (n + k) n
  have hvalidBase : gammaValid fp (11 * (n + k) + 23) :=
    gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid
  have hvalidRhs :
      gammaValid fp
        (householderQRRhsPanelGammaClosedGrowthIndex (n + k) n) :=
    gammaValid_mono fp (by simp [Theorem20_3.gammaIndex]) hvalid
  have hrho0 : 0 ≤ rho := by
    dsimp [rho, rhsRadius, Theorem20_3.rhsCoeff]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (gamma_nonneg fp hvalidRhs)
  have hden : 0 < 1 - rho := sub_pos.mpr (by simpa [rho] using hrho)
  have hnu0 : 0 ≤ inverseEnvelope fp (n + k) n := by
    dsimp [inverseEnvelope]
    exact inv_nonneg.mpr hden.le
  have hxi0 : 0 ≤ inverseDifferenceEnvelope fp (n + k) n := by
    dsimp [inverseDifferenceEnvelope]
    exact div_nonneg hrho0 hden.le
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta, metricDefectEnvelope]
    have htwo : 0 ≤ 2 - rho := by linarith
    exact div_nonneg (mul_nonneg hrho0 htwo) (sq_nonneg _)
  have hlam0 : 0 ≤ graphEnvelope fp (n + k) n := by
    dsimp [graphEnvelope]
    exact div_nonneg hdelta0
      (sub_nonneg.mpr (le_of_lt (by simpa [delta] using hdelta)))
  have hready : HouseholderQRPanelReady fp (n + k) n A :=
    HouseholderQRPanelReady_of_global_gammaValid
      fp (n + k) n (n + k) A le_rfl hvalidBase
  have hQ : IsOrthogonal (n + k)
      (fl_householderQRPanel_Q fp (n + k) n A) :=
    fl_householderQRPanel_Q_orthogonal fp (n + k) n A hready
  have hmetric :
      ∀ D : Matrix (Fin (n + k)) (Fin (n + k)) ℝ,
        frobNorm D ≤ rhsRadius fp (n + k) n →
          MetricGraphSmallness fp
            (fl_householderQRPanel_Q fp (n + k) n A) D := by
    intro D hD
    exact metricGraphSmallness_of_frobNorm_le fp _ D hQ hD hrho hdelta
  exact
    householder_qr_fl_backSub_matrix_only_backward_error_all_rhs
      fp A b hn hvalid hdiag hnu0 hxi0 hlam0 hmetric

end Theorem20_3_ZeroDeltaB

end NumStability
