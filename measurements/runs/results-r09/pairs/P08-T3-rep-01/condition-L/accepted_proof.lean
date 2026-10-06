import HighamBench.P08Definitions

namespace HighamBench

open scoped BigOperators

private lemma p08MatVec_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatAdd A B) x =
      p08VecAdd (p08MatVec A x) (p08MatVec B x) := by
  funext i
  simp only [p08MatVec, p08MatAdd, p08VecAdd]
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

private lemma p08MatVec_scale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatScale a A) x =
      p08VecScale a (p08MatVec A x) := by
  funext i
  simp only [p08MatVec, p08MatScale, p08VecScale, Finset.mul_sum]
  congr 1
  funext j
  ring

private lemma p08MatVec_mul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatMul A B) x = p08MatVec A (p08MatVec B x) := by
  funext i
  simp only [p08MatVec, p08MatMul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma p08MatVec_id {n : ℕ} (x : Fin n → ℝ) :
    p08MatVec (p08IdMatrix n) x = x := by
  funext i
  simp [p08MatVec, p08IdMatrix]

private lemma p08MatVec_vecAdd {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecAdd x y) =
      p08VecAdd (p08MatVec A x) (p08MatVec A y) := by
  funext i
  simp only [p08MatVec, p08VecAdd]
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

private lemma p08MatVec_vecScale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) :
    p08MatVec A (p08VecScale a x) =
      p08VecScale a (p08MatVec A x) := by
  funext i
  simp only [p08MatVec, p08VecScale, Finset.mul_sum]
  congr 1
  funext j
  ring

private lemma p08MatVec_vecSub {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecSub x y) =
      p08VecSub (p08MatVec A x) (p08MatVec A y) := by
  funext i
  simp only [p08MatVec, p08VecSub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private lemma p08MatVec_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p08MatNonnegative A)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ p08MatVec A x i := by
  intro i
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p08MatVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p08MatNonnegative A)
    {x y : Fin n → ℝ} (hxy : ∀ i, x i ≤ y i) :
    ∀ i, p08MatVec A x i ≤ p08MatVec A y i := by
  intro i
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08AbsMatrix_nonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) : p08MatNonnegative (p08AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p08MatMul_nonnegative {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) (hB : p08MatNonnegative B) :
    p08MatNonnegative (p08MatMul A B) := by
  intro i j
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

private lemma p08MatScale_nonnegative {n : ℕ}
    {a : ℝ} (ha : 0 ≤ a) {A : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) :
    p08MatNonnegative (p08MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private lemma p08_abs_matVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤
      p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  calc
    |p08MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
      simp only [p08MatVec, p08AbsMatrix, p08AbsVec, abs_mul]

private lemma p08_absVec_nonnegative {n : ℕ} (x : Fin n → ℝ) :
    ∀ i, 0 ≤ p08AbsVec x i := fun i ↦ abs_nonneg _

private lemma p08_vec_abs_add_le {n : ℕ} (x y : Fin n → ℝ) :
    ∀ i, p08AbsVec (p08VecAdd x y) i ≤
      p08VecAdd (p08AbsVec x) (p08AbsVec y) i := by
  intro i
  exact abs_add_le _ _

private lemma p08_inverse_action_left {n : ℕ}
    (run : P08IterativeRefinementRun n) (x : Fin n → ℝ) :
    p08MatVec run.Ainv (p08MatVec run.A x) = x := by
  rw [← p08MatVec_mul, run.inverse_left, p08MatVec_id]

private lemma p08_exactResidual_eq_neg_errors {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {constants : P08Lemma43Constants run norm dimensionBounds}
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) :
    p08ExactResidualAfterCorrection run m = fun i ↦
      -roundoff.residualError m i - roundoff.correctionError m i := by
  funext i
  have hr := congrFun (roundoff.residual_equation m) i
  have hc := congrFun (roundoff.correction_equation m) i
  simp only [p08ExactResidualAfterCorrection, p08VecSub, p08VecAdd,
    p08MatVec] at hr hc ⊢
  have hsub :
      (∑ j : Fin n, run.A i j * (run.iterate m j - run.correction m j)) =
        (∑ j : Fin n, run.A i j * run.iterate m j) -
          ∑ j : Fin n, run.A i j * run.correction m j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hsub]
  linear_combination -hr - hc

private lemma p08_residualUnitRoundoff_pos {n : ℕ}
    (run : P08IterativeRefinementRun n) :
    0 < p08ResidualUnitRoundoff run.precision run.u := by
  cases h : run.precision with
  | single =>
      simp [p08ResidualUnitRoundoff, h, run.u_pos]
  | double =>
      simp only [p08ResidualUnitRoundoff, h]
      exact pow_pos run.u_pos 2

private lemma p08_C6_action_identity {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (v : Fin n → ℝ) (i : Fin n) :
    run.u * p08MatVec
        (p08MatMul constants.C6 (p08AbsMatrix run.A)) v i =
      run.u * p08MatVec
          (p08MatMul constants.C2 (p08AbsMatrix run.A)) v i +
        (run.u + constants.c5 *
            p08ResidualUnitRoundoff run.precision run.u) *
          p08MatVec (p08AbsMatrix run.A) v i +
        run.u * (run.u + constants.c5 *
            p08ResidualUnitRoundoff run.precision run.u) *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C2 (p08AbsMatrix run.A))
              (p08AbsMatrix run.Ainv))
            (p08MatVec (p08AbsMatrix run.A) v) i := by
  rw [constants.C6_definition]
  simp only [p08MatVec_mul, p08MatVec_add, p08MatVec_scale,
    p08MatVec_id, p08MatVec_vecAdd, p08MatVec_vecScale,
    p08VecAdd, p08VecScale]
  field_simp [ne_of_gt run.u_pos]
  ring

private lemma p08_C7_action_identity {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (v : Fin n → ℝ) (i : Fin n) :
    p08ResidualUnitRoundoff run.precision run.u * run.u *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul (p08AbsMatrix run.A)
                (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A)) v i =
      run.u *
        (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsMatrix run.Ainv))
          (p08MatVec (p08AbsMatrix run.A) v) i := by
  rw [constants.C7_definition]
  simp only [p08MatVec_mul, p08MatVec_scale, p08VecScale]
  field_simp [ne_of_gt (p08_residualUnitRoundoff_pos run)]

private lemma p08_general_exact_residual_bound {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {constants : P08Lemma43Constants run norm dimensionBounds}
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run m i| ≤
      run.u * p08MatVec
        (p08MatMul constants.C6 (p08AbsMatrix run.A))
        (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
      (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution) i +
      p08ResidualUnitRoundoff run.precision run.u * run.u *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul (p08AbsMatrix run.A)
                (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) i := by
  let α : ℝ := n * p08ResidualUnitRoundoff run.precision run.u +
    p08Lemma43c3 run * run.u ^ 2
  let β : ℝ := run.u + constants.c5 *
    p08ResidualUnitRoundoff run.precision run.u
  let z : Fin n → ℝ := p08VecSub (run.iterate m) run.exactSolution
  let X : Fin n → ℝ := p08AbsVec run.exactSolution
  let Z : Fin n → ℝ := p08AbsVec z
  let M : Fin n → Fin n → ℝ :=
    p08MatMul
      (p08MatMul constants.C2 (p08AbsMatrix run.A))
      (p08AbsMatrix run.Ainv)
  have hk : 0 ≤ p08KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hcorrSmall :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    calc
      constants.c1 * run.u * p08KappaInverse run norm ≤
          constants.c8 * run.u * p08KappaInverse run norm := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right constants.c1_le_c8 run.u_pos.le) hk
      _ ≤ 1 / 2 := hsmall
  have hM : p08MatNonnegative M :=
    p08MatMul_nonnegative
      (p08MatMul_nonnegative constants.C2_nonnegative
        (p08AbsMatrix_nonnegative run.A))
      (p08AbsMatrix_nonnegative run.Ainv)
  have he : ∀ j,
      |roundoff.residualError m j| ≤
        α * p08MatVec (p08AbsMatrix run.A) X j +
        β * p08MatVec (p08AbsMatrix run.A) Z j := by
    intro j
    have hraw := roundoff.residual_error_bound m j
    have hAz := p08_abs_matVec_le run.A z j
    have huAz := mul_le_mul_of_nonneg_left hAz run.u_pos.le
    dsimp [α, β, z, X, Z] at hraw hAz huAz ⊢
    linarith
  have hMe :
      p08MatVec M (p08AbsVec (roundoff.residualError m)) i ≤
        α * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) X) i +
          β * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) Z) i := by
    calc
      p08MatVec M (p08AbsVec (roundoff.residualError m)) i ≤
          p08MatVec M
            (fun j ↦
              α * p08MatVec (p08AbsMatrix run.A) X j +
              β * p08MatVec (p08AbsMatrix run.A) Z j) i := by
        apply p08MatVec_mono hM
        exact he
      _ = α * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) X) i +
          β * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) Z) i := by
        change p08MatVec M
            (p08VecAdd
              (p08VecScale α (p08MatVec (p08AbsMatrix run.A) X))
              (p08VecScale β (p08MatVec (p08AbsMatrix run.A) Z))) i = _
        rw [p08MatVec_vecAdd, p08MatVec_vecScale, p08MatVec_vecScale]
        rfl
  have hfRaw := roundoff.correction_error_bound hcorrSmall m i
  have hf :
      |roundoff.correctionError m i| ≤
        run.u * p08MatVec
          (p08MatMul constants.C2 (p08AbsMatrix run.A)) Z i +
        run.u *
          (α * p08MatVec M
              (p08MatVec (p08AbsMatrix run.A) X) i +
            β * p08MatVec M
              (p08MatVec (p08AbsMatrix run.A) Z) i) := by
    have huMe := mul_le_mul_of_nonneg_left hMe run.u_pos.le
    dsimp [M, Z] at hfRaw ⊢
    linarith
  have hq :
      |p08ExactResidualAfterCorrection run m i| ≤
        |roundoff.residualError m i| +
          |roundoff.correctionError m i| := by
    rw [congrFun (p08_exactResidual_eq_neg_errors roundoff m) i]
    calc
      |-roundoff.residualError m i - roundoff.correctionError m i| =
          |roundoff.residualError m i + roundoff.correctionError m i| := by
        rw [show -roundoff.residualError m i - roundoff.correctionError m i =
          -(roundoff.residualError m i + roundoff.correctionError m i) by ring,
          abs_neg]
      _ ≤ _ := abs_add_le _ _
  have hcombined :
      |p08ExactResidualAfterCorrection run m i| ≤
        run.u * p08MatVec
            (p08MatMul constants.C2 (p08AbsMatrix run.A)) Z i +
          β * p08MatVec (p08AbsMatrix run.A) Z i +
          run.u * β * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) Z) i +
          α * p08MatVec (p08AbsMatrix run.A) X i +
          run.u * α * p08MatVec M
            (p08MatVec (p08AbsMatrix run.A) X) i := by
    have hei := he i
    linarith
  rw [p08_C6_action_identity constants Z i,
    p08_C7_action_identity constants X i]
  dsimp [α, β, z, X, Z, M] at hcombined ⊢
  linarith

private lemma p08_initialVector_identity {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08Lemma43InitialVector constants i =
      run.u * p08MatVec
        (p08MatMul constants.C6 (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i +
      (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution) i +
      p08ResidualUnitRoundoff run.precision run.u * run.u *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul (p08AbsMatrix run.A)
                (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) i := by
  unfold p08Lemma43InitialVector
  rw [constants.C10_definition]
  simp only [p08VecScale, p08MatVec_mul,
    p08MatVec_add, p08MatVec_scale, p08MatVec_id, p08VecAdd,
    p08VecScale]
  field_simp [ne_of_gt run.u_pos]

private lemma p08_initial_residual_bound {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {constants : P08Lemma43Constants run norm dimensionBounds}
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p08ExactResidualAfterCorrection run 0 i| ≤
      p08Lemma43InitialVector constants i := by
  have h := p08_general_exact_residual_bound roundoff hsmall 0 i
  rw [p08_initialVector_identity constants i]
  rw [run.iterate_zero] at h
  have hz :
      p08AbsVec (p08VecSub (fun _ : Fin n ↦ 0) run.exactSolution) =
        p08AbsVec run.exactSolution := by
    funext j
    simp [p08AbsVec, p08VecSub]
  rw [hz] at h
  exact h

private lemma p08_exactResidual_as_error_action {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) :
    p08ExactResidualAfterCorrection run m =
      p08MatVec run.A
        (p08VecSub
          (p08VecSub (run.iterate m) (run.correction m))
          run.exactSolution) := by
  unfold p08ExactResidualAfterCorrection
  rw [p08MatVec_vecSub, p08MatVec_vecSub, run.exact_system]
  rw [← p08MatVec_vecSub]

private lemma p08_next_error_identity {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) :
    p08VecSub (run.iterate (m + 1)) run.exactSolution =
      p08VecAdd
        (p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m))
        (run.updateError (m + 1)) := by
  rw [p08_exactResidual_as_error_action]
  rw [p08_inverse_action_left]
  rw [run.update_equation]
  funext i
  simp only [p08VecSub, p08VecAdd]
  ring

private lemma p08_corrected_iterate_abs_bound {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate m i - run.correction m i| ≤
      |run.exactSolution i| +
        p08MatVec (p08AbsMatrix run.Ainv)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
  have hres := p08_abs_matVec_le run.Ainv
    (p08ExactResidualAfterCorrection run m) i
  have hEq := congrFun
    (p08_inverse_action_left run
      (p08VecSub
        (p08VecSub (run.iterate m) (run.correction m))
        run.exactSolution)) i
  rw [← p08_exactResidual_as_error_action run m] at hEq
  simp only [p08VecSub] at hEq
  have hsum := abs_add_le (run.exactSolution i)
    (p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i)
  calc
    |run.iterate m i - run.correction m i| =
        |run.exactSolution i +
          p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i| := by
      congr 1
      linarith
    _ ≤ |run.exactSolution i| +
        |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i| := hsum
    _ ≤ _ := add_le_add_right hres _

private lemma p08_next_error_abs_bound {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |p08VecSub (run.iterate (m + 1)) run.exactSolution i| ≤
      run.u * |run.exactSolution i| +
        (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
  have hidentity := congrFun (p08_next_error_identity run m) i
  have hadd := abs_add_le
    (p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i)
    (run.updateError (m + 1) i)
  simp only [p08VecSub, p08VecAdd] at hidentity
  have hadd' :
      |p08VecSub (run.iterate (m + 1)) run.exactSolution i| ≤
        |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i| +
          |run.updateError (m + 1) i| := by
    simp only [p08VecSub]
    rw [hidentity]
    exact hadd
  have hinv := p08_abs_matVec_le run.Ainv
    (p08ExactResidualAfterCorrection run m) i
  have hupd := run.update_error_bound m i
  have hy := p08_corrected_iterate_abs_bound run m i
  have huy := mul_le_mul_of_nonneg_left hy run.u_pos.le
  linarith

private lemma p08_propagation_action_identity {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (v : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08Lemma43Propagation constants) v i =
      run.u * (1 + run.u) *
        p08MatVec
          (p08MatMul constants.C6 (p08AbsMatrix run.A))
          (p08MatVec (p08AbsMatrix run.Ainv) v) i := by
  unfold p08Lemma43Propagation
  rw [constants.C8_definition]
  simp only [p08MatVec_scale, p08MatVec_mul, p08VecScale]
  ring

private lemma p08_forcing_identity {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08Lemma43RecurrenceForcing constants i =
      run.u ^ 2 *
          p08MatVec
            (p08MatMul constants.C6 (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i +
        (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution) i +
        p08ResidualUnitRoundoff run.precision run.u * run.u *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C7
                (p08MatMul (p08AbsMatrix run.A)
                  (p08AbsMatrix run.Ainv)))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i := by
  unfold p08Lemma43RecurrenceForcing
  rw [constants.C9_definition]
  simp only [p08VecAdd, p08VecScale, p08MatVec_mul, p08MatVec_add,
    p08MatVec_scale, p08MatVec_id]
  ring

private lemma p08_residual_recurrence {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {constants : P08Lemma43Constants run norm dimensionBounds}
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
      p08MatVec (p08Lemma43Propagation constants)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        p08Lemma43RecurrenceForcing constants i := by
  let L : Fin n → Fin n → ℝ :=
    p08MatMul constants.C6 (p08AbsMatrix run.A)
  let Q : Fin n → ℝ :=
    p08AbsVec (p08ExactResidualAfterCorrection run m)
  let X : Fin n → ℝ := p08AbsVec run.exactSolution
  have hL : p08MatNonnegative L :=
    p08MatMul_nonnegative constants.C6_nonnegative
      (p08AbsMatrix_nonnegative run.A)
  have hnext : ∀ j,
      p08AbsVec
          (p08VecSub (run.iterate (m + 1)) run.exactSolution) j ≤
        p08VecAdd
          (p08VecScale run.u X)
          (p08VecScale (1 + run.u)
            (p08MatVec (p08AbsMatrix run.Ainv) Q)) j := by
    intro j
    exact p08_next_error_abs_bound run m j
  have hLnext := p08MatVec_mono hL hnext i
  have hLnext' :
      run.u * p08MatVec L
          (p08AbsVec
            (p08VecSub (run.iterate (m + 1)) run.exactSolution)) i ≤
        run.u ^ 2 * p08MatVec L X i +
          run.u * (1 + run.u) *
            p08MatVec L
              (p08MatVec (p08AbsMatrix run.Ainv) Q) i := by
    have hu := mul_le_mul_of_nonneg_left hLnext run.u_pos.le
    rw [p08MatVec_vecAdd, p08MatVec_vecScale,
      p08MatVec_vecScale] at hu
    simp only [p08VecAdd, p08VecScale] at hu
    nlinarith
  have hgen := p08_general_exact_residual_bound
    roundoff hsmall (m + 1) i
  rw [p08_propagation_action_identity constants Q i,
    p08_forcing_identity constants i]
  dsimp [L, Q, X] at hLnext' ⊢
  linarith

private lemma p08_C11_action_fixed {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (v : Fin n → ℝ)
    (i : Fin n) :
    p08MatVec constants.C11 v i =
      p08MatVec constants.C9 v i +
        run.u * p08MatVec constants.C8
          (p08MatVec (p08AbsMatrix run.A)
            (p08MatVec (p08AbsMatrix run.Ainv)
              (p08MatVec constants.C11 v))) i := by
  have h := congrArg (fun B ↦ p08MatVec B v i)
    constants.C11_fixed_point
  simpa only [p08VecAdd, p08VecScale, p08MatVec_mul, p08MatVec_add,
    p08MatVec_scale] using h

private lemma p08_C12_action_fixed {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (v : Fin n → ℝ)
    (i : Fin n) :
    p08MatVec constants.C12 v i =
      n * p08MatVec constants.C8 v i +
        p08MatVec constants.C7 v i +
        run.u * p08MatVec constants.C8
          (p08MatVec (p08AbsMatrix run.A)
            (p08MatVec (p08AbsMatrix run.Ainv)
              (p08MatVec constants.C12 v))) i := by
  have h := congrArg (fun B ↦ p08MatVec B v i)
    constants.C12_fixed_point
  simpa only [p08VecAdd, p08VecScale, p08MatVec_mul, p08MatVec_add,
    p08MatVec_scale] using h

private lemma p08_stationary_fixed_point {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08Lemma43StationaryVector constants i =
      p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43StationaryVector constants) i +
        p08Lemma43RecurrenceForcing constants i := by
  have h11 := p08_C11_action_fixed constants
    (p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution)) i
  have h12 := p08_C12_action_fixed constants
    (p08MatVec (p08AbsMatrix run.A)
      (p08MatVec (p08AbsMatrix run.Ainv)
        (p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution)))) i
  unfold p08Lemma43StationaryVector p08Lemma43Propagation
    p08Lemma43RecurrenceForcing
  simp only [p08VecAdd, p08VecScale, p08MatVec_mul, p08MatVec_add,
    p08MatVec_scale, p08MatVec_vecAdd, p08MatVec_vecScale]
  linear_combination
    run.u ^ 2 * h11 +
      (p08ResidualUnitRoundoff run.precision run.u * run.u) * h12

private lemma p08_stationary_nonnegative {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    ∀ i, 0 ≤ p08Lemma43StationaryVector constants i := by
  intro i
  have hA := p08AbsMatrix_nonnegative run.A
  have hAi := p08AbsMatrix_nonnegative run.Ainv
  have hX := p08_absVec_nonnegative run.exactSolution
  have hAX := p08MatVec_nonnegative hA hX
  have h11A := p08MatMul_nonnegative constants.C11_nonnegative hA
  have h11AX := p08MatVec_nonnegative h11A hX
  have h12AAiA := p08MatMul_nonnegative
    (p08MatMul_nonnegative constants.C12_nonnegative
      (p08MatMul_nonnegative hA hAi)) hA
  have h12AAiAX := p08MatVec_nonnegative h12AAiA hX
  have hub := (p08_residualUnitRoundoff_pos run).le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold p08Lemma43StationaryVector
  simp only [p08VecAdd, p08VecScale]
  exact add_nonneg
    (mul_nonneg (mul_nonneg hn hub) (hAX i))
    (add_nonneg
      (mul_nonneg (sq_nonneg run.u) (h11AX i))
      (mul_nonneg (mul_nonneg hub run.u_pos.le) (h12AAiAX i)))

private lemma p08_propagation_nonnegative {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    p08MatNonnegative (p08Lemma43Propagation constants) := by
  unfold p08Lemma43Propagation
  apply p08MatScale_nonnegative run.u_pos.le
  exact p08MatMul_nonnegative constants.C8_nonnegative
    (p08MatMul_nonnegative (p08AbsMatrix_nonnegative run.A)
      (p08AbsMatrix_nonnegative run.Ainv))

private lemma p08_bound_recurrence {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (m : ℕ) (i : Fin n) :
    p08Lemma43Bound constants (m + 1) i =
      p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43Bound constants m) i +
        p08Lemma43RecurrenceForcing constants i := by
  unfold p08Lemma43Bound
  rw [p08MatVec_vecAdd, ← p08MatVec_mul]
  change
    p08MatVec
          (p08MatMul (p08Lemma43Propagation constants)
            (p08MatPow (p08Lemma43Propagation constants) m))
          (p08Lemma43InitialVector constants) i +
        p08Lemma43StationaryVector constants i = _
  rw [p08_stationary_fixed_point constants i]
  simp only [p08VecAdd]
  ring

theorem p08_t3_lemma_4_3_exact_residual_bound
    {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff :
      P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall :
      constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2) :
    ∀ m i,
      |p08ExactResidualAfterCorrection run m i| ≤
        p08Lemma43Bound constants m i := by
  -- PROOF_START P08-T3-H001
  have hP := p08_propagation_nonnegative constants
  have hS := p08_stationary_nonnegative constants
  intro m
  induction m with
  | zero =>
      intro i
      have h0 := p08_initial_residual_bound roundoff hsmall i
      calc
        |p08ExactResidualAfterCorrection run 0 i| ≤
            p08Lemma43InitialVector constants i := h0
        _ ≤ p08Lemma43InitialVector constants i +
              p08Lemma43StationaryVector constants i :=
          le_add_of_nonneg_right (hS i)
        _ = p08Lemma43Bound constants 0 i := by
          unfold p08Lemma43Bound
          simp only [p08MatPow, p08MatVec_id, p08VecAdd]
  | succ m ih =>
      intro i
      have hrec := p08_residual_recurrence roundoff hsmall m i
      have hmono := p08MatVec_mono hP ih i
      calc
        |p08ExactResidualAfterCorrection run (m + 1) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
                (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
              p08Lemma43RecurrenceForcing constants i := hrec
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
                (p08Lemma43Bound constants m) i +
              p08Lemma43RecurrenceForcing constants i :=
          add_le_add_left hmono _
        _ = p08Lemma43Bound constants (m + 1) i :=
          (p08_bound_recurrence constants m i).symm

end HighamBench
