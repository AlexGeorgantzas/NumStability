import HighamBench.P08Definitions

namespace HighamBench

private lemma p08_matVec_add {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecAdd x y) i =
      p08MatVec A x i + p08MatVec A y i := by
  simp [p08MatVec, p08VecAdd, mul_add, Finset.sum_add_distrib]

private lemma p08_matVec_add_fun {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecAdd x y) =
      p08VecAdd (p08MatVec A x) (p08MatVec A y) := by
  funext i
  exact p08_matVec_add A x y i

private lemma p08_matVec_sub {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecSub x y) i =
      p08MatVec A x i - p08MatVec A y i := by
  simp [p08MatVec, p08VecSub, mul_sub, Finset.sum_sub_distrib]

private lemma p08_matVec_scale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecScale a x) i =
      a * p08MatVec A x i := by
  simp only [p08MatVec, p08VecScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p08_matVec_scale_fun {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) :
    p08MatVec A (p08VecScale a x) =
      p08VecScale a (p08MatVec A x) := by
  funext i
  exact p08_matVec_scale A a x i

private lemma p08_matVec_mul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatMul A B) x i =
      p08MatVec A (p08MatVec B x) i := by
  unfold p08MatVec p08MatMul
  calc
    (∑ j : Fin n, (∑ k : Fin n, A i k * B k j) * x j) =
        ∑ j : Fin n, ∑ k : Fin n, (A i k * B k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin n, (A i k * B k j) * x j := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, A i k * (∑ j : Fin n, B k j * x j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

private lemma p08_matVec_mul_fun {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatMul A B) x =
      p08MatVec A (p08MatVec B x) := by
  funext i
  exact p08_matVec_mul A B x i

private lemma p08_matVec_matAdd {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatAdd A B) x i =
      p08MatVec A x i + p08MatVec B x i := by
  simp [p08MatVec, p08MatAdd, add_mul, Finset.sum_add_distrib]

private lemma p08_matVec_matScale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatScale a A) x i =
      a * p08MatVec A x i := by
  simp only [p08MatVec, p08MatScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p08_id_action {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08IdMatrix n) x i = x i := by
  simp [p08MatVec, p08IdMatrix]

private lemma p08_matVec_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hx : ∀ i, 0 ≤ x i) (i : Fin n) :
    0 ≤ p08MatVec A x i := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p08_matVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x y : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p08MatVec A x i ≤ p08MatVec A y i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08_abs_matVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤
      p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  calc
    |p08MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| := by
      exact Finset.abs_sum_le_sum_abs (fun j ↦ A i j * x j) Finset.univ
    _ = p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
      simp [p08MatVec, p08AbsMatrix, p08AbsVec, abs_mul]

private lemma p08_absMatrix_nonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    p08MatNonnegative (p08AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p08_matMul_nonnegative {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) (hB : p08MatNonnegative B) :
    p08MatNonnegative (p08MatMul A B) := by
  intro i j
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

private lemma p08_matScale_nonnegative {n : ℕ}
    {a : ℝ} {A : Fin n → Fin n → ℝ}
    (ha : 0 ≤ a) (hA : p08MatNonnegative A) :
    p08MatNonnegative (p08MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private lemma p08_matPow_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p08MatNonnegative A) :
    ∀ m, p08MatNonnegative (p08MatPow A m) := by
  intro m
  induction m with
  | zero =>
      intro i j
      simp only [p08MatPow, p08IdMatrix]
      split <;> simp
  | succ m ih =>
      simpa [p08MatPow] using p08_matMul_nonnegative hA ih

private lemma p08_inverse_left_action {n : ℕ}
    (run : P08IterativeRefinementRun n) (z : Fin n → ℝ) (i : Fin n) :
    p08MatVec run.Ainv (p08MatVec run.A z) i = z i := by
  rw [← p08_matVec_mul, run.inverse_left, p08_id_action]

private lemma p08_exact_residual_eq_neg_errors {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    p08ExactResidualAfterCorrection run m i =
      -roundoff.residualError m i - roundoff.correctionError m i := by
  have hr := congrFun (roundoff.residual_equation m) i
  have hc := congrFun (roundoff.correction_equation m) i
  simp only [p08VecAdd, p08VecSub] at hr hc
  unfold p08ExactResidualAfterCorrection
  simp only [p08VecSub]
  rw [p08_matVec_sub]
  linarith

private lemma p08_inverse_exact_residual {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i =
      run.iterate m i - run.correction m i - run.exactSolution i := by
  have hq : p08ExactResidualAfterCorrection run m =
      p08MatVec run.A
        (p08VecSub (p08VecSub (run.iterate m) (run.correction m))
          run.exactSolution) := by
    funext j
    unfold p08ExactResidualAfterCorrection
    simp only [p08VecSub]
    rw [p08_matVec_sub run.A
      (p08VecSub (run.iterate m) (run.correction m)) run.exactSolution j]
    rw [p08_matVec_sub run.A (run.iterate m) (run.correction m) j]
    have hb := congrFun run.exact_system j
    linarith
  rw [hq, p08_inverse_left_action]
  rfl

private lemma p08_next_error_identity {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    run.iterate (m + 1) i - run.exactSolution i =
      p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i +
        run.updateError (m + 1) i := by
  have hu := congrFun (run.update_equation m) i
  simp only [p08VecAdd, p08VecSub] at hu
  rw [p08_inverse_exact_residual]
  linarith

private lemma p08_residual_unit_nonnegative {n : ℕ}
    (run : P08IterativeRefinementRun n) :
    0 ≤ p08ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp [p08ResidualUnitRoundoff, le_of_lt run.u_pos, sq_nonneg]

private lemma p08_residual_unit_pos {n : ℕ}
    (run : P08IterativeRefinementRun n) :
    0 < p08ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp [p08ResidualUnitRoundoff, run.u_pos]

private lemma p08_propagation_nonnegative {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    p08MatNonnegative (p08Lemma43Propagation constants) := by
  unfold p08Lemma43Propagation
  apply p08_matScale_nonnegative (le_of_lt run.u_pos)
  exact p08_matMul_nonnegative constants.C8_nonnegative
    (p08_matMul_nonnegative (p08_absMatrix_nonnegative run.A)
      (p08_absMatrix_nonnegative run.Ainv))

private lemma p08_initial_nonnegative {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) (i : Fin n) :
    0 ≤ p08Lemma43InitialVector constants i := by
  unfold p08Lemma43InitialVector p08VecScale
  apply mul_nonneg (le_of_lt run.u_pos)
  apply p08_matVec_nonnegative
  · exact p08_matMul_nonnegative constants.C10_nonnegative
      (p08_absMatrix_nonnegative run.A)
  · intro j
    exact abs_nonneg _

private lemma p08_stationary_nonnegative {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) (i : Fin n) :
    0 ≤ p08Lemma43StationaryVector constants i := by
  let Aa := p08AbsMatrix run.A
  let Ai := p08AbsMatrix run.Ainv
  let X := p08AbsVec run.exactSolution
  let ub := p08ResidualUnitRoundoff run.precision run.u
  have hAa : p08MatNonnegative Aa := p08_absMatrix_nonnegative run.A
  have hAi : p08MatNonnegative Ai := p08_absMatrix_nonnegative run.Ainv
  have hX : ∀ j, 0 ≤ X j := fun j ↦ abs_nonneg _
  have hub : 0 ≤ ub := p08_residual_unit_nonnegative run
  have hAX : ∀ j, 0 ≤ p08MatVec Aa X j :=
    fun j ↦ p08_matVec_nonnegative hAa hX j
  have hCX (C : Fin n → Fin n → ℝ) (hC : p08MatNonnegative C) :
      0 ≤ p08MatVec (p08MatMul C Aa) X i := by
    exact p08_matVec_nonnegative (p08_matMul_nonnegative hC hAa) hX i
  have hlong (C : Fin n → Fin n → ℝ) (hC : p08MatNonnegative C) :
      0 ≤ p08MatVec (p08MatMul (p08MatMul C (p08MatMul Aa Ai)) Aa) X i := by
    exact p08_matVec_nonnegative
      (p08_matMul_nonnegative
        (p08_matMul_nonnegative hC (p08_matMul_nonnegative hAa hAi)) hAa) hX i
  unfold p08Lemma43StationaryVector
  simp only [p08VecAdd, p08VecScale]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have h1 : 0 ≤ (n : ℝ) * ub * p08MatVec Aa X i :=
    mul_nonneg (mul_nonneg hn hub) (hAX i)
  have h2 : 0 ≤ run.u ^ 2 *
      p08MatVec (p08MatMul constants.C11 Aa) X i :=
    mul_nonneg (sq_nonneg run.u) (hCX constants.C11 constants.C11_nonnegative)
  have h3 : 0 ≤ ub * run.u *
      p08MatVec (p08MatMul (p08MatMul constants.C12 (p08MatMul Aa Ai)) Aa) X i :=
    mul_nonneg (mul_nonneg hub hu) (hlong constants.C12 constants.C12_nonnegative)
  simpa [Aa, Ai, X, ub] using add_nonneg h1 (add_nonneg h2 h3)

private lemma p08_stationary_fixed_point {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) (i : Fin n) :
    p08Lemma43StationaryVector constants i =
      p08Lemma43RecurrenceForcing constants i +
        p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43StationaryVector constants) i := by
  unfold p08Lemma43StationaryVector p08Lemma43RecurrenceForcing
    p08Lemma43Propagation
  nth_rewrite 1 [constants.C11_fixed_point]
  nth_rewrite 1 [constants.C12_fixed_point]
  simp only [p08VecAdd, p08VecScale, p08_matVec_matAdd,
    p08_matVec_matScale, p08_matVec_add,
    p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  simp only [p08_matVec_matAdd, p08_matVec_matScale,
    p08_matVec_add, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  simp only [p08_matVec_matAdd, p08_matVec_matScale,
    p08_matVec_add, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  rw [p08_matVec_mul_fun
    (p08MatMul constants.C12
      (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
    (p08AbsMatrix run.A) (p08AbsVec run.exactSolution)]
  rw [p08_matVec_mul_fun constants.C11 (p08AbsMatrix run.A)
    (p08AbsVec run.exactSolution)]
  rw [p08_matVec_mul_fun constants.C12
    (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))
    (p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution))]
  ring

private lemma p08_master_residual_bound {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run m i| ≤
      run.u * p08MatVec constants.C6
        (p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution))) i +
      (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution) i +
      run.u *
        (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec
          (p08MatMul constants.C2
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
          (p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution)) i := by
  let Aa := p08AbsMatrix run.A
  let Ai := p08AbsMatrix run.Ainv
  let X := p08AbsVec run.exactSolution
  let E := p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)
  let R := p08AbsVec (roundoff.residualError m)
  let ub := p08ResidualUnitRoundoff run.precision run.u
  let alpha := (n : ℝ) * ub + p08Lemma43c3 run * run.u ^ 2
  let ae := p08MatVec Aa E
  let ax := p08MatVec Aa X
  let K := p08MatMul constants.C2 (p08MatMul Aa Ai)
  let rb : Fin n → ℝ :=
    p08VecAdd (p08VecScale alpha ax)
      (p08VecScale (constants.c5 * ub + run.u) ae)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hkappa : 0 ≤ p08KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hc1small :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    have hp : 0 ≤ run.u * p08KappaInverse run norm :=
      mul_nonneg hu hkappa
    have := mul_le_mul_of_nonneg_right constants.c1_le_c8 hp
    nlinarith
  have hrb : ∀ j, R j ≤ rb j := by
    intro j
    have hr := roundoff.residual_error_bound m j
    have ha := p08_abs_matVec_le run.A
      (p08VecSub (run.iterate m) run.exactSolution) j
    change |roundoff.residualError m j| ≤ _ at hr
    change |roundoff.residualError m j| ≤ _
    change R j ≤ rb j
    dsimp [rb, alpha, ax, ae, R, Aa, X, E, ub,
      p08AbsVec, p08VecAdd, p08VecScale]
    nlinarith
  have hK : p08MatNonnegative K := by
    exact p08_matMul_nonnegative constants.C2_nonnegative
      (p08_matMul_nonnegative (p08_absMatrix_nonnegative run.A)
        (p08_absMatrix_nonnegative run.Ainv))
  have hKR : p08MatVec K R i ≤ p08MatVec K rb i :=
    p08_matVec_mono hK hrb i
  have hd := roundoff.correction_error_bound hc1small m i
  have hd' : |roundoff.correctionError m i| ≤
      run.u * p08MatVec (p08MatMul constants.C2 Aa) E i +
        run.u * p08MatVec K rb i := by
    calc
      |roundoff.correctionError m i| ≤
          run.u * p08MatVec (p08MatMul constants.C2 Aa) E i +
          run.u * p08MatVec
            (p08MatMul (p08MatMul constants.C2 Aa) Ai) R i := by
              simpa [Aa, Ai, E, R] using hd
      _ = run.u * p08MatVec (p08MatMul constants.C2 Aa) E i +
          run.u * p08MatVec K R i := by
            dsimp [K]
            simp_rw [p08_matVec_mul]
            rw [p08_matVec_mul_fun Aa Ai R]
      _ ≤ run.u * p08MatVec (p08MatMul constants.C2 Aa) E i +
          run.u * p08MatVec K rb i := by
            gcongr
  rw [p08_exact_residual_eq_neg_errors run norm dimensionBounds
    constants roundoff m i]
  calc
    |-roundoff.residualError m i - roundoff.correctionError m i| ≤
        |roundoff.residualError m i| +
          |roundoff.correctionError m i| := by
            simpa only [abs_neg] using
              (abs_add_le (-roundoff.residualError m i)
                (-roundoff.correctionError m i))
    _ ≤ rb i +
        (run.u * p08MatVec (p08MatMul constants.C2 Aa) E i +
          run.u * p08MatVec K rb i) := add_le_add (hrb i) hd'
    _ = run.u * p08MatVec constants.C6 ae i +
        alpha * ax i + run.u * alpha * p08MatVec K ax i := by
          rw [constants.C6_definition]
          dsimp [rb, K]
          simp only [p08VecAdd, p08VecScale, p08_matVec_matAdd, p08_matVec_matScale,
            p08_matVec_add, p08_matVec_scale, p08_id_action]
          simp_rw [p08_matVec_mul]
          field_simp [ne_of_gt run.u_pos]
          ring
    _ = _ := by
      rfl

private lemma p08_initial_residual_bound {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p08ExactResidualAfterCorrection run 0 i| ≤
      p08Lemma43InitialVector constants i := by
  have hm := p08_master_residual_bound dimensionBounds run norm constants
    roundoff hsmall 0 i
  have hE : p08AbsVec
      (p08VecSub (run.iterate 0) run.exactSolution) =
      p08AbsVec run.exactSolution := by
    funext j
    rw [run.iterate_zero]
    simp [p08AbsVec, p08VecSub]
  rw [hE] at hm
  calc
    |p08ExactResidualAfterCorrection run 0 i| ≤ _ := hm
    _ = p08Lemma43InitialVector constants i := by
      unfold p08Lemma43InitialVector
      rw [constants.C10_definition, constants.C7_definition]
      simp only [p08VecScale]
      simp_rw [p08_matVec_mul, p08_matVec_matAdd,
        p08_matVec_matScale, p08_id_action]
      simp_rw [p08_matVec_mul, p08_matVec_matScale]
      field_simp [ne_of_gt run.u_pos,
        ne_of_gt (p08_residual_unit_pos run)]

private lemma p08_residual_recurrence {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
      p08MatVec (p08Lemma43Propagation constants)
        (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
      p08Lemma43RecurrenceForcing constants i := by
  let Aa := p08AbsMatrix run.A
  let Ai := p08AbsMatrix run.Ainv
  let X := p08AbsVec run.exactSolution
  let Q := p08AbsVec (p08ExactResidualAfterCorrection run m)
  let E := p08AbsVec
    (p08VecSub (run.iterate (m + 1)) run.exactSolution)
  let EB := p08VecAdd
    (p08VecScale (1 + run.u) (p08MatVec Ai Q))
    (p08VecScale run.u X)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hE : ∀ j, E j ≤ EB j := by
    intro j
    have hnext := p08_next_error_identity run m j
    have hq := p08_inverse_exact_residual run m j
    have hainv := p08_abs_matVec_le run.Ainv
      (p08ExactResidualAfterCorrection run m) j
    have hupd := run.update_error_bound m j
    have htri1 := abs_add_le
      (p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) j)
      (run.updateError (m + 1) j)
    have htri2 := abs_add_le (run.exactSolution j)
      (p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) j)
    change |run.iterate (m + 1) j - run.exactSolution j| ≤ _
    dsimp [EB, E, Q, X, Ai, p08AbsVec, p08VecAdd, p08VecScale]
    rw [hnext]
    have hy : |run.iterate m j - run.correction m j| ≤
        |run.exactSolution j| +
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) j := by
      have hyid : run.iterate m j - run.correction m j =
          run.exactSolution j +
            p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) j := by
        rw [hq]
        ring
      rw [hyid]
      exact htri2.trans (add_le_add (le_refl _) hainv)
    nlinarith
  have hAa : p08MatNonnegative Aa := p08_absMatrix_nonnegative run.A
  have hAE : ∀ j, p08MatVec Aa E j ≤ p08MatVec Aa EB j :=
    fun j ↦ p08_matVec_mono hAa hE j
  have hC : p08MatVec constants.C6 (p08MatVec Aa E) i ≤
      p08MatVec constants.C6 (p08MatVec Aa EB) i :=
    p08_matVec_mono constants.C6_nonnegative hAE i
  have hEBaction :
      p08MatVec constants.C6 (p08MatVec Aa EB) i =
        (1 + run.u) *
          p08MatVec constants.C6 (p08MatVec (p08MatMul Aa Ai) Q) i +
        run.u * p08MatVec constants.C6 (p08MatVec Aa X) i := by
    rw [show EB = p08VecAdd
      (p08VecScale (1 + run.u) (p08MatVec Ai Q))
      (p08VecScale run.u X) from rfl]
    rw [p08_matVec_add_fun, p08_matVec_scale_fun,
      p08_matVec_scale_fun]
    rw [p08_matVec_add, p08_matVec_scale, p08_matVec_scale]
    rw [p08_matVec_mul_fun Aa Ai Q]
  have hm := p08_master_residual_bound dimensionBounds run norm constants
    roundoff hsmall (m + 1) i
  calc
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤ _ := hm
    _ ≤ run.u * p08MatVec constants.C6 (p08MatVec Aa EB) i +
        (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec Aa X i +
        run.u *
          (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec
            (p08MatMul constants.C2 (p08MatMul Aa Ai))
            (p08MatVec Aa X) i := by
              dsimp [Aa, Ai, X, E] at hC ⊢
              gcongr
    _ = p08MatVec (p08Lemma43Propagation constants) Q i +
        p08Lemma43RecurrenceForcing constants i := by
      rw [hEBaction]
      unfold p08Lemma43Propagation p08Lemma43RecurrenceForcing
      rw [constants.C8_definition, constants.C9_definition,
        constants.C7_definition]
      dsimp [Q, X, Aa, Ai]
      simp only [p08VecAdd, p08VecScale]
      simp_rw [p08_matVec_mul, p08_matVec_matAdd,
        p08_matVec_matScale, p08_id_action]
      simp_rw [p08_matVec_mul, p08_matVec_matScale]
      field_simp [ne_of_gt (p08_residual_unit_pos run)]
      ring
    _ = _ := by rfl

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
  intro m
  induction m with
  | zero =>
      intro i
      have h0 := p08_initial_residual_bound dimensionBounds run norm
        constants roundoff hsmall i
      have hs := p08_stationary_nonnegative constants i
      unfold p08Lemma43Bound
      simp only [p08MatPow, p08VecAdd, p08_id_action]
      linarith
  | succ m ih =>
      intro i
      have hr := p08_residual_recurrence dimensionBounds run norm constants
        roundoff hsmall m i
      have hP := p08_propagation_nonnegative constants
      have hmono := p08_matVec_mono hP ih i
      calc
        |p08ExactResidualAfterCorrection run (Nat.succ m) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
            p08Lemma43RecurrenceForcing constants i := by
              simpa [Nat.succ_eq_add_one] using hr
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
              (p08Lemma43Bound constants m) i +
            p08Lemma43RecurrenceForcing constants i :=
              add_le_add hmono (le_refl _)
        _ = p08Lemma43Bound constants (Nat.succ m) i := by
          have hs := p08_stationary_fixed_point constants i
          unfold p08Lemma43Bound
          simp only [p08VecAdd]
          rw [p08_matVec_add]
          rw [← p08_matVec_mul]
          simp only [p08MatPow]
          linarith

end HighamBench
