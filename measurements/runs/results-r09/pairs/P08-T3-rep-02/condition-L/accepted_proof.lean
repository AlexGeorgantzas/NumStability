import HighamBench.P08Definitions

namespace HighamBench

open scoped BigOperators

private lemma p08_matVec_add_apply {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatAdd A B) x i = p08MatVec A x i + p08MatVec B x i := by
  simp only [p08MatVec, p08MatAdd, add_mul, Finset.sum_add_distrib]

private lemma p08_matVec_scale_apply {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatScale a A) x i = a * p08MatVec A x i := by
  simp only [p08MatVec, p08MatScale, Finset.mul_sum, mul_assoc]

private lemma p08_matVec_mul_apply {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatMul A B) x i = p08MatVec A (p08MatVec B x) i := by
  simp only [p08MatVec, p08MatMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

private lemma p08_matVec_mul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatMul A B) x = p08MatVec A (p08MatVec B x) := by
  funext i
  exact p08_matVec_mul_apply A B x i

private lemma p08_matVec_id_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08IdMatrix n) x i = x i := by
  simp [p08MatVec, p08IdMatrix]

private lemma p08_matVec_vecAdd_apply {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecAdd x y) i = p08MatVec A x i + p08MatVec A y i := by
  simp only [p08MatVec, p08VecAdd, mul_add, Finset.sum_add_distrib]

private lemma p08_matVec_vecScale_apply {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecScale a x) i = a * p08MatVec A x i := by
  simp only [p08MatVec, p08VecScale]
  calc
    (∑ j, A i j * (a * x j)) = ∑ j, a * (A i j * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = a * ∑ j, A i j * x j := (Finset.mul_sum _ _ _).symm

private lemma p08_abs_matVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤ p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  rw [p08MatVec, p08MatVec]
  calc
    |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := by simp only [abs_mul]
    _ = ∑ j, p08AbsMatrix A i j * p08AbsVec x j := by rfl

private lemma p08_matVec_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hx : ∀ i, 0 ≤ x i) (i : Fin n) :
    0 ≤ p08MatVec A x i := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p08_matVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x y : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p08MatVec A x i ≤ p08MatVec A y i := by
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08_absVec_nonnegative {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ p08AbsVec x i := abs_nonneg _

private lemma p08_absMatrix_nonnegative {n : ℕ} (A : Fin n → Fin n → ℝ) :
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

private lemma p08_lemma43_one_step {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcsmall : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run m i| ≤
      run.u * p08MatVec
        (p08MatMul constants.C6 (p08AbsMatrix run.A))
        (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
      n * p08ResidualUnitRoundoff run.precision run.u *
        p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution) i +
      p08Lemma43c3 run * run.u ^ 2 *
        p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution) i +
      p08ResidualUnitRoundoff run.precision run.u * run.u *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) i := by
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let absz := p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  let alpha := n * ubar + p08Lemma43c3 run * run.u ^ 2
  let beta := constants.c5 * ubar + run.u
  let E := p08VecAdd
    (p08VecScale alpha (p08MatVec absA absx))
    (p08VecScale beta (p08MatVec absA absz))
  have he : ∀ j, |roundoff.residualError m j| ≤ E j := by
    intro j
    have he0 := roundoff.residual_error_bound m j
    have hAz := p08_abs_matVec_le run.A
      (p08VecSub (run.iterate m) run.exactSolution) j
    have hu : 0 ≤ run.u := le_of_lt run.u_pos
    dsimp [E, alpha, beta, absA, absx, absz, ubar,
      p08VecAdd, p08VecScale] at he0 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hAz hu]
  have hH : p08MatNonnegative
      (p08MatMul
        (p08MatMul constants.C2 (p08AbsMatrix run.A))
        (p08AbsMatrix run.Ainv)) :=
    p08_matMul_nonnegative
      (p08_matMul_nonnegative constants.C2_nonnegative
        (p08_absMatrix_nonnegative run.A))
      (p08_absMatrix_nonnegative run.Ainv)
  have hHE :
      p08MatVec
          (p08MatMul
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsMatrix run.Ainv))
          (p08AbsVec (roundoff.residualError m)) i ≤
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsMatrix run.Ainv)) E i := by
    apply p08_matVec_mono hH
    intro j
    exact he j
  have hc0 := roundoff.correction_error_bound hcsmall m i
  have hc : |roundoff.correctionError m i| ≤
      run.u * p08MatVec
        (p08MatMul constants.C2 (p08AbsMatrix run.A)) absz i +
      run.u * p08MatVec
        (p08MatMul
          (p08MatMul constants.C2 (p08AbsMatrix run.A))
          (p08AbsMatrix run.Ainv)) E i := by
    have hu : 0 ≤ run.u := le_of_lt run.u_pos
    dsimp [absz] at hc0 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hHE hu]
  have hq : p08ExactResidualAfterCorrection run m i =
      -(roundoff.residualError m i + roundoff.correctionError m i) := by
    have hr := congrFun (roundoff.residual_equation m) i
    have hcorr := congrFun (roundoff.correction_equation m) i
    dsimp [p08ExactResidualAfterCorrection, p08VecSub, p08VecAdd] at hr hcorr ⊢
    simp only [p08MatVec, p08VecSub, mul_sub, Finset.sum_sub_distrib] at hr hcorr ⊢
    linarith
  rw [hq, abs_neg]
  calc
    |roundoff.residualError m i + roundoff.correctionError m i| ≤
        |roundoff.residualError m i| + |roundoff.correctionError m i| :=
      abs_add_le _ _
    _ ≤ E i +
        (run.u * p08MatVec
          (p08MatMul constants.C2 (p08AbsMatrix run.A)) absz i +
        run.u * p08MatVec
          (p08MatMul
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsMatrix run.Ainv)) E i) := add_le_add (he i) hc
    _ = run.u * p08MatVec
        (p08MatMul constants.C6 (p08AbsMatrix run.A)) absz i +
      n * ubar * p08MatVec absA absx i +
      p08Lemma43c3 run * run.u ^ 2 * p08MatVec absA absx i +
      ubar * run.u *
        p08MatVec
          (p08MatMul
            (p08MatMul constants.C7 (p08MatMul absA absAinv)) absA)
          absx i := by
      rw [constants.C6_definition, constants.C7_definition]
      dsimp [E, alpha, beta, ubar, absA, absAinv, absx, absz]
      simp only [p08_matVec_mul_apply, p08_matVec_add_apply,
        p08_matVec_scale_apply, p08_matVec_id_apply,
        p08_matVec_vecAdd_apply, p08_matVec_vecScale_apply]
      simp only [p08_matVec_mul]
      simp only [p08VecAdd, p08VecScale]
      have hu : run.u ≠ 0 := ne_of_gt run.u_pos
      have hubar : p08ResidualUnitRoundoff run.precision run.u ≠ 0 := by
        cases hprec : run.precision <;>
          simp [p08ResidualUnitRoundoff, hprec, hu]
      field_simp
      ring
    _ = _ := by rfl

private lemma p08_lemma43_iterate_error {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |p08VecSub (run.iterate (m + 1)) run.exactSolution i| ≤
      (1 + run.u) *
        p08MatVec (p08AbsMatrix run.Ainv)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
      run.u * p08AbsVec run.exactSolution i := by
  let q := p08ExactResidualAfterCorrection run m
  let z := p08VecSub
    (p08VecSub (run.iterate m) (run.correction m)) run.exactSolution
  have hq : q = p08MatVec run.A z := by
    funext j
    have hexact := congrFun run.exact_system j
    dsimp [q, z, p08ExactResidualAfterCorrection, p08VecSub] at hexact ⊢
    simp only [p08MatVec, p08VecSub, mul_sub, Finset.sum_sub_distrib] at hexact ⊢
    linarith
  have hinv : p08MatVec run.Ainv q = z := by
    rw [hq, ← p08_matVec_mul]
    rw [run.inverse_left]
    funext j
    exact p08_matVec_id_apply z j
  have hupdate := run.update_error_bound m i
  have haiq := p08_abs_matVec_le run.Ainv q i
  have hcorr : |p08VecSub (run.iterate m) (run.correction m) i| ≤
      p08AbsVec run.exactSolution i +
        p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q) i := by
    have hz : p08VecSub (run.iterate m) (run.correction m) i =
        run.exactSolution i + p08MatVec run.Ainv q i := by
      have hi := congrFun hinv i
      dsimp [z, p08VecSub] at hi ⊢
      linarith
    rw [hz]
    calc
      |run.exactSolution i + p08MatVec run.Ainv q i| ≤
          |run.exactSolution i| + |p08MatVec run.Ainv q i| := abs_add_le _ _
      _ ≤ p08AbsVec run.exactSolution i +
          p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q) i := by
        dsimp [p08AbsVec]
        linarith
  have hznext : p08VecSub (run.iterate (m + 1)) run.exactSolution i =
      p08MatVec run.Ainv q i + run.updateError (m + 1) i := by
    have hu := congrFun (run.update_equation m) i
    have hi := congrFun hinv i
    dsimp [z, p08VecAdd, p08VecSub] at hu hi ⊢
    linarith
  rw [hznext]
  have hu0 : 0 ≤ run.u := le_of_lt run.u_pos
  have hu_update : |run.updateError (m + 1) i| ≤
      run.u * (p08AbsVec run.exactSolution i +
        p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q) i) := by
    dsimp [p08VecSub] at hcorr
    nlinarith [mul_le_mul_of_nonneg_left hcorr hu0]
  calc
    |p08MatVec run.Ainv q i + run.updateError (m + 1) i| ≤
        |p08MatVec run.Ainv q i| + |run.updateError (m + 1) i| :=
      abs_add_le _ _
    _ ≤ (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q) i +
        run.u * p08AbsVec run.exactSolution i := by
      nlinarith
    _ = _ := by rfl

private lemma p08_lemma43_recurrence {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcsmall : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
      p08MatVec (p08Lemma43Propagation constants)
        (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
      p08Lemma43RecurrenceForcing constants i := by
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let absq := p08AbsVec (p08ExactResidualAfterCorrection run m)
  let W := p08VecAdd
    (p08VecScale (1 + run.u) (p08MatVec absAinv absq))
    (p08VecScale run.u absx)
  have hW : ∀ j,
      p08AbsVec (p08VecSub (run.iterate (m + 1)) run.exactSolution) j ≤ W j := by
    intro j
    exact p08_lemma43_iterate_error run m j
  have hC6A : p08MatNonnegative (p08MatMul constants.C6 absA) :=
    p08_matMul_nonnegative constants.C6_nonnegative
      (p08_absMatrix_nonnegative run.A)
  have hmono :
      p08MatVec (p08MatMul constants.C6 absA)
          (p08AbsVec (p08VecSub (run.iterate (m + 1)) run.exactSolution)) i ≤
        p08MatVec (p08MatMul constants.C6 absA) W i :=
    p08_matVec_mono hC6A hW i
  have hstep := p08_lemma43_one_step dimensionBounds run norm constants
    roundoff hcsmall (m + 1) i
  calc
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
        run.u * p08MatVec (p08MatMul constants.C6 absA)
            (p08AbsVec (p08VecSub (run.iterate (m + 1)) run.exactSolution)) i +
          n * p08ResidualUnitRoundoff run.precision run.u *
            p08MatVec absA absx i +
          p08Lemma43c3 run * run.u ^ 2 * p08MatVec absA absx i +
          p08ResidualUnitRoundoff run.precision run.u * run.u *
            p08MatVec
              (p08MatMul
                (p08MatMul constants.C7 (p08MatMul absA absAinv)) absA)
              absx i := hstep
    _ ≤ run.u * p08MatVec (p08MatMul constants.C6 absA) W i +
          n * p08ResidualUnitRoundoff run.precision run.u *
            p08MatVec absA absx i +
          p08Lemma43c3 run * run.u ^ 2 * p08MatVec absA absx i +
          p08ResidualUnitRoundoff run.precision run.u * run.u *
            p08MatVec
              (p08MatMul
                (p08MatMul constants.C7 (p08MatMul absA absAinv)) absA)
              absx i := by
      have hu : 0 ≤ run.u := le_of_lt run.u_pos
      nlinarith [mul_le_mul_of_nonneg_left hmono hu]
    _ = p08MatVec (p08Lemma43Propagation constants) absq i +
        p08Lemma43RecurrenceForcing constants i := by
      dsimp [p08Lemma43Propagation, p08Lemma43RecurrenceForcing,
        W, absA, absAinv, absx, absq]
      rw [constants.C8_definition, constants.C9_definition]
      simp only [p08_matVec_mul_apply, p08_matVec_add_apply,
        p08_matVec_scale_apply, p08_matVec_id_apply,
        p08_matVec_vecAdd_apply, p08_matVec_vecScale_apply,
        p08VecAdd, p08VecScale]
      simp only [p08_matVec_mul]
      ring

private lemma p08_lemma43_initial {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcsmall : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p08ExactResidualAfterCorrection run 0 i| ≤
      p08Lemma43InitialVector constants i := by
  have hz0 :
      p08AbsVec (p08VecSub (run.iterate 0) run.exactSolution) =
        p08AbsVec run.exactSolution := by
    funext j
    rw [run.iterate_zero]
    simp [p08AbsVec, p08VecSub]
  have hstep := p08_lemma43_one_step dimensionBounds run norm constants
    roundoff hcsmall 0 i
  rw [hz0] at hstep
  calc
    |p08ExactResidualAfterCorrection run 0 i| ≤
        run.u * p08MatVec
            (p08MatMul constants.C6 (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i +
          n * p08ResidualUnitRoundoff run.precision run.u *
            p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution) i +
          p08Lemma43c3 run * run.u ^ 2 *
            p08MatVec (p08AbsMatrix run.A) (p08AbsVec run.exactSolution) i +
          p08ResidualUnitRoundoff run.precision run.u * run.u *
            p08MatVec
              (p08MatMul
                (p08MatMul constants.C7
                  (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
                (p08AbsMatrix run.A))
              (p08AbsVec run.exactSolution) i := hstep
    _ = p08Lemma43InitialVector constants i := by
      dsimp [p08Lemma43InitialVector]
      rw [constants.C10_definition]
      simp only [p08VecScale]
      simp only [p08_matVec_mul_apply, p08_matVec_add_apply,
        p08_matVec_scale_apply, p08_matVec_id_apply]
      simp only [p08_matVec_mul]
      have hu : run.u ≠ 0 := ne_of_gt run.u_pos
      field_simp
      ring

private lemma p08_lemma43_stationary_fixed_point {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08Lemma43StationaryVector constants i =
      p08Lemma43RecurrenceForcing constants i +
        p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43StationaryVector constants) i := by
  dsimp [p08Lemma43StationaryVector, p08Lemma43RecurrenceForcing,
    p08Lemma43Propagation]
  conv_lhs =>
    rw [constants.C11_fixed_point, constants.C12_fixed_point]
  simp only [p08VecAdd, p08VecScale, p08_matVec_mul_apply,
    p08_matVec_add_apply, p08_matVec_scale_apply, p08_matVec_id_apply,
    p08_matVec_vecAdd_apply, p08_matVec_vecScale_apply]
  simp only [p08_matVec_mul]
  ring

private lemma p08_lemma43_propagation_nonnegative {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    p08MatNonnegative (p08Lemma43Propagation constants) := by
  apply p08_matScale_nonnegative (le_of_lt run.u_pos)
  exact p08_matMul_nonnegative constants.C8_nonnegative
    (p08_matMul_nonnegative
      (p08_absMatrix_nonnegative run.A)
      (p08_absMatrix_nonnegative run.Ainv))

private lemma p08_lemma43_stationary_nonnegative {n : ℕ}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    0 ≤ p08Lemma43StationaryVector constants i := by
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p08ResidualUnitRoundoff run.precision run.u := by
    cases run.precision <;> simp [p08ResidualUnitRoundoff] <;> positivity
  have hax : 0 ≤ p08MatVec (p08AbsMatrix run.A)
      (p08AbsVec run.exactSolution) i :=
    p08_matVec_nonnegative (p08_absMatrix_nonnegative run.A)
      (p08_absVec_nonnegative run.exactSolution) i
  have h11 : 0 ≤ p08MatVec
      (p08MatMul constants.C11 (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution) i :=
    p08_matVec_nonnegative
      (p08_matMul_nonnegative constants.C11_nonnegative
        (p08_absMatrix_nonnegative run.A))
      (p08_absVec_nonnegative run.exactSolution) i
  have h12 : 0 ≤ p08MatVec
      (p08MatMul
        (p08MatMul constants.C12
          (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
        (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution) i := by
    apply p08_matVec_nonnegative
      (p08_matMul_nonnegative
        (p08_matMul_nonnegative constants.C12_nonnegative
          (p08_matMul_nonnegative
            (p08_absMatrix_nonnegative run.A)
            (p08_absMatrix_nonnegative run.Ainv)))
        (p08_absMatrix_nonnegative run.A))
      (p08_absVec_nonnegative run.exactSolution)
  dsimp [p08Lemma43StationaryVector, p08VecAdd, p08VecScale]
  exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hubar) hax)
    (add_nonneg (mul_nonneg (sq_nonneg run.u) h11)
      (mul_nonneg (mul_nonneg hubar hu) h12))

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
  have hkappa : 0 ≤ p08KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hcsmall :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    calc
      constants.c1 * run.u * p08KappaInverse run norm =
          constants.c1 * (run.u * p08KappaInverse run norm) := by ring
      _ ≤ constants.c8 * (run.u * p08KappaInverse run norm) :=
        mul_le_mul_of_nonneg_right constants.c1_le_c8
          (mul_nonneg (le_of_lt run.u_pos) hkappa)
      _ = constants.c8 * run.u * p08KappaInverse run norm := by ring
      _ ≤ 1 / 2 := hsmall
  have hP := p08_lemma43_propagation_nonnegative constants
  intro m
  induction m with
  | zero =>
      intro i
      have hinit := p08_lemma43_initial dimensionBounds run norm constants
        roundoff hcsmall i
      have hstationary := p08_lemma43_stationary_nonnegative constants i
      dsimp [p08Lemma43Bound]
      simp only [p08MatPow, p08_matVec_id_apply, p08VecAdd]
      linarith
  | succ m ih =>
      intro i
      have hrec := p08_lemma43_recurrence dimensionBounds run norm constants
        roundoff hcsmall m i
      have hmono :
          p08MatVec (p08Lemma43Propagation constants)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i ≤
            p08MatVec (p08Lemma43Propagation constants)
              (p08Lemma43Bound constants m) i := by
        apply p08_matVec_mono hP
        intro j
        exact ih j
      calc
        |p08ExactResidualAfterCorrection run (m + 1) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
                (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
              p08Lemma43RecurrenceForcing constants i := hrec
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
                (p08Lemma43Bound constants m) i +
              p08Lemma43RecurrenceForcing constants i :=
          add_le_add hmono (le_refl _)
        _ = p08Lemma43Bound constants (m + 1) i := by
          have hfixed := p08_lemma43_stationary_fixed_point constants i
          dsimp [p08Lemma43Bound]
          simp only [p08MatPow, p08_matVec_vecAdd_apply]
          simp only [p08VecAdd, p08_matVec_mul_apply]
          linarith

end HighamBench
