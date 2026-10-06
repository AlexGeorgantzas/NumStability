import HighamBench.P08Definitions

namespace HighamBench

open scoped BigOperators

private lemma p08_t3_matVec_id {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08IdMatrix n) x i = x i := by
  simp [p08MatVec, p08IdMatrix]

private lemma p08_t3_matVec_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatAdd A B) x i = p08MatVec A x i + p08MatVec B x i := by
  simp [p08MatVec, p08MatAdd, add_mul, Finset.sum_add_distrib]

private lemma p08_t3_matVec_add_fun {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatAdd A B) x =
      p08VecAdd (p08MatVec A x) (p08MatVec B x) := by
  funext i
  exact p08_t3_matVec_add A B x i

private lemma p08_t3_matVec_scale {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatScale a A) x i = a * p08MatVec A x i := by
  simp [p08MatVec, p08MatScale, Finset.mul_sum, mul_assoc]

private lemma p08_t3_matVec_scale_fun {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatScale a A) x = p08VecScale a (p08MatVec A x) := by
  funext i
  exact p08_t3_matVec_scale a A x i

private lemma p08_t3_matVec_vecAdd {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecAdd x y) i =
      p08MatVec A x i + p08MatVec A y i := by
  simp [p08MatVec, p08VecAdd, mul_add, Finset.sum_add_distrib]

private lemma p08_t3_matVec_vecScale {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecScale a x) i = a * p08MatVec A x i := by
  simp [p08MatVec, p08VecScale, Finset.mul_sum, mul_assoc, mul_left_comm]

private lemma p08_t3_matVec_mul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatMul A B) x i = p08MatVec A (p08MatVec B x) i := by
  simp only [p08MatVec, p08MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma p08_t3_matVec_mul_fun {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatMul A B) x = p08MatVec A (p08MatVec B x) := by
  funext i
  exact p08_t3_matVec_mul A B x i

private lemma p08_t3_matVec_linear3 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a b c : ℝ)
    (x y z : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (fun k => a * x k + b * y k + c * z k) i =
      a * p08MatVec A x i + b * p08MatVec A y i +
        c * p08MatVec A z i := by
  simp [p08MatVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

private lemma p08_t3_matVec_linear2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a b : ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (fun k => a * x k + b * y k) i =
      a * p08MatVec A x i + b * p08MatVec A y i := by
  simp [p08MatVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    mul_left_comm]

private lemma p08_t3_matVec_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hx : ∀ j, 0 ≤ x j) (i : Fin n) :
    0 ≤ p08MatVec A x i := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hA i j) (hx j)

private lemma p08_t3_matVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x y : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hxy : ∀ j, x j ≤ y j) (i : Fin n) :
    p08MatVec A x i ≤ p08MatVec A y i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08_t3_matMul_nonnegative {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) (hB : p08MatNonnegative B) :
    p08MatNonnegative (p08MatMul A B) := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hA i k) (hB k j)

private lemma p08_t3_matScale_nonnegative {n : ℕ}
    {a : ℝ} {A : Fin n → Fin n → ℝ}
    (ha : 0 ≤ a) (hA : p08MatNonnegative A) :
    p08MatNonnegative (p08MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private lemma p08_t3_absMatrix_nonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) : p08MatNonnegative (p08AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p08_t3_abs_matVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤
      p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  simpa [p08MatVec, p08AbsMatrix, p08AbsVec, abs_mul] using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun j : Fin n => A i j * x j))

private lemma p08_t3_matVec_sub {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecSub x y) i = p08MatVec A x i - p08MatVec A y i := by
  simp [p08MatVec, p08VecSub, mul_sub, Finset.sum_sub_distrib]

private lemma p08_t3_matVec_sub_fun {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecSub x y) =
      p08VecSub (p08MatVec A x) (p08MatVec A y) := by
  funext i
  exact p08_t3_matVec_sub A x y i

private lemma p08_t3_inverse_residual {n : ℕ}
    (run : P08IterativeRefinementRun n) (y : Fin n → ℝ) (i : Fin n) :
    p08MatVec run.Ainv
        (p08VecSub (p08MatVec run.A y) run.b) i =
      y i - run.exactSolution i := by
  rw [← run.exact_system]
  calc
    p08MatVec run.Ainv
        (p08VecSub (p08MatVec run.A y)
          (p08MatVec run.A run.exactSolution)) i =
        p08MatVec run.Ainv (p08MatVec run.A y) i -
          p08MatVec run.Ainv (p08MatVec run.A run.exactSolution) i :=
      p08_t3_matVec_sub _ _ _ _
    _ = p08MatVec run.Ainv
          (p08MatVec run.A (p08VecSub y run.exactSolution)) i := by
      rw [p08_t3_matVec_sub_fun, p08_t3_matVec_sub]
    _ = p08MatVec (p08MatMul run.Ainv run.A)
          (p08VecSub y run.exactSolution) i := by
      rw [p08_t3_matVec_mul]
    _ = p08MatVec (p08IdMatrix n)
          (p08VecSub y run.exactSolution) i := by rw [run.inverse_left]
    _ = y i - run.exactSolution i := by
      simpa [p08VecSub] using
        p08_t3_matVec_id (p08VecSub y run.exactSolution) i

private lemma p08_t3_forward_error_succ_bound {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u * |run.exactSolution i| := by
  let y := p08VecSub (run.iterate m) (run.correction m)
  have hy :
      p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i =
        y i - run.exactSolution i := by
    exact p08_t3_inverse_residual run y i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hupd := run.update_error_bound m i
  have hupdate :
      run.iterate (m + 1) i - run.exactSolution i =
        p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i +
          run.updateError (m + 1) i := by
    have heq := congrFun (run.update_equation m) i
    change p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i =
      (run.iterate m i - run.correction m i) - run.exactSolution i at hy
    simp only [p08VecAdd, p08VecSub] at heq
    rw [heq, hy]
    ring
  have hyabs := p08_t3_abs_matVec run.Ainv
    (p08ExactResidualAfterCorrection run m) i
  have hyvalue :
      |run.iterate m i - run.correction m i| ≤
        |run.exactSolution i| +
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
    change p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i =
      (run.iterate m i - run.correction m i) - run.exactSolution i at hy
    calc
      |run.iterate m i - run.correction m i|
          = |run.exactSolution i +
              p08MatVec run.Ainv
                (p08ExactResidualAfterCorrection run m) i| := by
              congr 1
              linarith
      _ ≤ |run.exactSolution i| +
            |p08MatVec run.Ainv
              (p08ExactResidualAfterCorrection run m) i| := abs_add_le _ _
      _ ≤ |run.exactSolution i| +
            p08MatVec (p08AbsMatrix run.Ainv)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
              linarith
  rw [hupdate]
  calc
    |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i +
        run.updateError (m + 1) i|
        ≤ |p08MatVec run.Ainv
              (p08ExactResidualAfterCorrection run m) i| +
            |run.updateError (m + 1) i| := abs_add_le _ _
    _ ≤ p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
          run.u * (|run.exactSolution i| +
            p08MatVec (p08AbsMatrix run.Ainv)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i) := by
          have hupdate_le := hupd.trans
            (mul_le_mul_of_nonneg_left hyvalue hu)
          linarith
    _ = (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u * |run.exactSolution i| := by ring

private lemma p08_t3_exact_residual_identity {n : ℕ}
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
  rw [p08ExactResidualAfterCorrection]
  change p08MatVec run.A
      (p08VecSub (run.iterate m) (run.correction m)) i - run.b i = _
  rw [p08_t3_matVec_sub]
  linarith

private lemma p08_t3_current_error_bound {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcorr : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run m i| ≤
      run.u * p08MatVec
          (p08MatMul constants.C6 (p08AbsMatrix run.A))
          (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
        (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution) i +
        run.u *
          (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec
            (p08MatMul
              (p08MatMul
                (p08MatMul constants.C2 (p08AbsMatrix run.A))
                (p08AbsMatrix run.Ainv))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i := by
  let D := p08AbsMatrix run.A
  let E := p08AbsMatrix run.Ainv
  let z := p08VecSub (run.iterate m) run.exactSolution
  let xabs := p08AbsVec run.exactSolution
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  let alpha := n * ubar + p08Lemma43c3 run * run.u ^ 2
  let beta := constants.c5 * ubar
  let M := p08MatMul (p08MatMul constants.C2 D) E
  let R : Fin n → ℝ := fun k =>
    alpha * p08MatVec D xabs k +
      beta * p08MatVec D (p08AbsVec z) k +
      run.u * |p08MatVec run.A z k|
  let R' : Fin n → ℝ := fun k =>
    alpha * p08MatVec D xabs k +
      beta * p08MatVec D (p08AbsVec z) k +
      run.u * p08MatVec D (p08AbsVec z) k
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hD : p08MatNonnegative D := p08_t3_absMatrix_nonnegative run.A
  have hE : p08MatNonnegative E := p08_t3_absMatrix_nonnegative run.Ainv
  have hC2D : p08MatNonnegative (p08MatMul constants.C2 D) :=
    p08_t3_matMul_nonnegative constants.C2_nonnegative hD
  have hM : p08MatNonnegative M :=
    p08_t3_matMul_nonnegative hC2D hE
  have hR : ∀ k, |roundoff.residualError m k| ≤ R k := by
    intro k
    simpa [R, alpha, beta, ubar, D, z, xabs] using
      roundoff.residual_error_bound m k
  have hMR := p08_t3_matVec_mono hM hR i
  have hg := roundoff.correction_error_bound hcorr m i
  change |roundoff.correctionError m i| ≤
      run.u * p08MatVec (p08MatMul constants.C2 D) (p08AbsVec z) i +
        run.u * p08MatVec M
          (p08AbsVec (roundoff.residualError m)) i at hg
  have hMRu :
      run.u * p08MatVec M (p08AbsVec (roundoff.residualError m)) i ≤
        run.u * p08MatVec M R i :=
    mul_le_mul_of_nonneg_left hMR hu
  have htri :
      |p08ExactResidualAfterCorrection run m i| ≤
        |roundoff.residualError m i| +
          |roundoff.correctionError m i| := by
    rw [p08_t3_exact_residual_identity run norm dimensionBounds constants
      roundoff m i]
    rw [show -roundoff.residualError m i - roundoff.correctionError m i =
      -(roundoff.residualError m i + roundoff.correctionError m i) by ring,
      abs_neg]
    exact abs_add_le _ _
  have hqR :
      |p08ExactResidualAfterCorrection run m i| ≤
        R i + run.u *
          p08MatVec (p08MatMul constants.C2 D) (p08AbsVec z) i +
          run.u * p08MatVec M R i := by
    have := hR i
    linarith
  have hRR' : ∀ k, R k ≤ R' k := by
    intro k
    have ha := p08_t3_abs_matVec run.A z k
    change |p08MatVec run.A z k| ≤ p08MatVec D (p08AbsVec z) k at ha
    dsimp [R, R']
    nlinarith
  have hMRR' := p08_t3_matVec_mono hM hRR' i
  have hMRR'u : run.u * p08MatVec M R i ≤
      run.u * p08MatVec M R' i :=
    mul_le_mul_of_nonneg_left hMRR' hu
  calc
    |p08ExactResidualAfterCorrection run m i|
        ≤ R i + run.u *
            p08MatVec (p08MatMul constants.C2 D) (p08AbsVec z) i +
            run.u * p08MatVec M R i := hqR
    _ ≤ R' i + run.u *
            p08MatVec (p08MatMul constants.C2 D) (p08AbsVec z) i +
            run.u * p08MatVec M R' i := by
          have := hRR' i
          linarith
    _ = run.u * p08MatVec
          (p08MatMul constants.C6 (p08AbsMatrix run.A))
          (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
        (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution) i +
        run.u *
          (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec
            (p08MatMul
              (p08MatMul
                (p08MatMul constants.C2 (p08AbsMatrix run.A))
                (p08AbsMatrix run.Ainv))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i := by
      rw [constants.C6_definition]
      simp only [R', M, alpha, beta, ubar, D, E, z, xabs,
        p08_t3_matVec_add, p08_t3_matVec_scale, p08_t3_matVec_mul,
        p08_t3_matVec_mul_fun, p08_t3_matVec_linear3, p08_t3_matVec_id]
      field_simp [ne_of_gt run.u_pos]
      ring

private lemma p08_t3_ubar_pos {n : ℕ} (run : P08IterativeRefinementRun n) :
    0 < p08ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp only [p08ResidualUnitRoundoff]
  · exact run.u_pos
  · exact sq_pos_of_pos run.u_pos

private lemma p08_t3_initial_residual_bound {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcorr : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p08ExactResidualAfterCorrection run 0 i| ≤
      p08Lemma43InitialVector constants i := by
  have hcur := p08_t3_current_error_bound dimensionBounds run norm constants
    roundoff hcorr 0 i
  calc
    |p08ExactResidualAfterCorrection run 0 i| ≤
        run.u * p08MatVec
            (p08MatMul constants.C6 (p08AbsMatrix run.A))
            (p08AbsVec
              (p08VecSub (run.iterate 0) run.exactSolution)) i +
          (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec run.exactSolution) i +
          run.u *
            (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec
              (p08MatMul
                (p08MatMul
                  (p08MatMul constants.C2 (p08AbsMatrix run.A))
                  (p08AbsMatrix run.Ainv))
                (p08AbsMatrix run.A))
              (p08AbsVec run.exactSolution) i := hcur
    _ = p08Lemma43InitialVector constants i := by
      have hz :
          p08AbsVec (p08VecSub (run.iterate 0) run.exactSolution) =
            p08AbsVec run.exactSolution := by
        funext j
        rw [run.iterate_zero]
        simp [p08AbsVec, p08VecSub]
      rw [hz]
      simp only [p08Lemma43InitialVector, p08VecScale]
      rw [constants.C10_definition, constants.C7_definition]
      simp only [p08_t3_matVec_add, p08_t3_matVec_scale, p08_t3_matVec_mul,
        p08_t3_matVec_mul_fun, p08_t3_matVec_id]
      field_simp [ne_of_gt run.u_pos, ne_of_gt (p08_t3_ubar_pos run)]

private lemma p08_t3_residual_recurrence {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hcorr : constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
      p08MatVec (p08Lemma43Propagation constants)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        p08Lemma43RecurrenceForcing constants i := by
  let D := p08AbsMatrix run.A
  let E := p08AbsMatrix run.Ainv
  let xabs := p08AbsVec run.exactSolution
  let qabs := p08AbsVec (p08ExactResidualAfterCorrection run m)
  let znext := p08VecSub (run.iterate (m + 1)) run.exactSolution
  let Y : Fin n → ℝ := fun j =>
    (1 + run.u) * p08MatVec E qabs j + run.u * xabs j
  let H := p08MatMul constants.C6 D
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hD : p08MatNonnegative D := p08_t3_absMatrix_nonnegative run.A
  have hH : p08MatNonnegative H :=
    p08_t3_matMul_nonnegative constants.C6_nonnegative hD
  have hz : ∀ j, p08AbsVec znext j ≤ Y j := by
    intro j
    simpa [znext, Y, E, qabs, xabs, p08AbsVec, p08VecSub] using
      p08_t3_forward_error_succ_bound run m j
  have hHY := p08_t3_matVec_mono hH hz i
  have hHYu : run.u * p08MatVec H (p08AbsVec znext) i ≤
      run.u * p08MatVec H Y i :=
    mul_le_mul_of_nonneg_left hHY hu
  have hcur := p08_t3_current_error_bound dimensionBounds run norm constants
    roundoff hcorr (m + 1) i
  change |p08ExactResidualAfterCorrection run (m + 1) i| ≤
      run.u * p08MatVec H (p08AbsVec znext) i +
        (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec D xabs i +
        run.u *
          (n * p08ResidualUnitRoundoff run.precision run.u +
            p08Lemma43c3 run * run.u ^ 2) *
          p08MatVec
            (p08MatMul
              (p08MatMul (p08MatMul constants.C2 D) E) D) xabs i at hcur
  calc
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
        run.u * p08MatVec H Y i +
          (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec D xabs i +
          run.u *
            (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec
              (p08MatMul
                (p08MatMul (p08MatMul constants.C2 D) E) D) xabs i := by
          linarith
    _ = p08MatVec (p08Lemma43Propagation constants)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        p08Lemma43RecurrenceForcing constants i := by
      simp only [p08Lemma43Propagation, p08Lemma43RecurrenceForcing,
        p08VecAdd, p08VecScale]
      rw [constants.C8_definition, constants.C9_definition,
        constants.C7_definition]
      simp only [p08_t3_matVec_add,
        p08_t3_matVec_scale, p08_t3_matVec_mul,
        p08_t3_matVec_mul_fun, p08_t3_matVec_id,
        p08_t3_matVec_linear2, H, Y, D, E, qabs, xabs]
      field_simp [ne_of_gt (p08_t3_ubar_pos run)]
      ring

private lemma p08_t3_stationary_fixed_point {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08MatVec (p08Lemma43Propagation constants)
        (p08Lemma43StationaryVector constants) i +
      p08Lemma43RecurrenceForcing constants i =
        p08Lemma43StationaryVector constants i := by
  simp only [p08Lemma43Propagation, p08Lemma43StationaryVector,
    p08Lemma43RecurrenceForcing, p08VecAdd, p08VecScale]
  conv_rhs =>
    rw [constants.C11_fixed_point, constants.C12_fixed_point]
  simp only [p08_t3_matVec_add, p08_t3_matVec_scale,
    p08_t3_matVec_mul, p08_t3_matVec_mul_fun, p08_t3_matVec_id,
    p08_t3_matVec_vecAdd, p08_t3_matVec_vecScale,
    p08_t3_matVec_add_fun, p08_t3_matVec_scale_fun]
  ring

private lemma p08_t3_propagation_nonnegative {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    p08MatNonnegative (p08Lemma43Propagation constants) := by
  have hD := p08_t3_absMatrix_nonnegative run.A
  have hE := p08_t3_absMatrix_nonnegative run.Ainv
  have hDE := p08_t3_matMul_nonnegative hD hE
  have hC8DE := p08_t3_matMul_nonnegative constants.C8_nonnegative hDE
  exact p08_t3_matScale_nonnegative (le_of_lt run.u_pos) hC8DE

private lemma p08_t3_stationary_nonnegative {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    ∀ i, 0 ≤ p08Lemma43StationaryVector constants i := by
  let D := p08AbsMatrix run.A
  let E := p08AbsMatrix run.Ainv
  let xabs := p08AbsVec run.exactSolution
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p08ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p08_t3_ubar_pos run)
  have hD : p08MatNonnegative D := p08_t3_absMatrix_nonnegative run.A
  have hE : p08MatNonnegative E := p08_t3_absMatrix_nonnegative run.Ainv
  have hx : ∀ j, 0 ≤ xabs j := by
    intro j
    exact abs_nonneg _
  have hDE := p08_t3_matMul_nonnegative hD hE
  have hC11D := p08_t3_matMul_nonnegative constants.C11_nonnegative hD
  have hC12DE := p08_t3_matMul_nonnegative constants.C12_nonnegative hDE
  have hC12DED := p08_t3_matMul_nonnegative hC12DE hD
  intro i
  have hDx := p08_t3_matVec_nonneg hD hx i
  have hC11Dx := p08_t3_matVec_nonneg hC11D hx i
  have hC12DEDx := p08_t3_matVec_nonneg hC12DED hx i
  simp only [p08Lemma43StationaryVector, p08VecAdd, p08VecScale]
  positivity

private lemma p08_t3_bound_succ {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (m : ℕ) (i : Fin n) :
    p08MatVec (p08Lemma43Propagation constants)
        (p08Lemma43Bound constants m) i +
      p08Lemma43RecurrenceForcing constants i =
        p08Lemma43Bound constants (m + 1) i := by
  have hfix := p08_t3_stationary_fixed_point dimensionBounds run norm
    constants i
  simp only [p08Lemma43Bound, p08VecAdd, p08MatPow,
    p08_t3_matVec_vecAdd, p08_t3_matVec_mul]
  linarith

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
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hkappa : 0 ≤ p08KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hcorr :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    calc
      constants.c1 * run.u * p08KappaInverse run norm =
          constants.c1 * (run.u * p08KappaInverse run norm) := by ring
      _ ≤ constants.c8 * (run.u * p08KappaInverse run norm) :=
        mul_le_mul_of_nonneg_right constants.c1_le_c8 (mul_nonneg hu hkappa)
      _ = constants.c8 * run.u * p08KappaInverse run norm := by ring
      _ ≤ 1 / 2 := hsmall
  have hP := p08_t3_propagation_nonnegative dimensionBounds run norm constants
  have hS := p08_t3_stationary_nonnegative dimensionBounds run norm constants
  intro m
  induction m with
  | zero =>
      intro i
      have hinit := p08_t3_initial_residual_bound dimensionBounds run norm
        constants roundoff hcorr i
      calc
        |p08ExactResidualAfterCorrection run 0 i|
            ≤ p08Lemma43InitialVector constants i := hinit
        _ ≤ p08Lemma43InitialVector constants i +
              p08Lemma43StationaryVector constants i :=
          le_add_of_nonneg_right (hS i)
        _ = p08Lemma43Bound constants 0 i := by
          simp only [p08Lemma43Bound, p08MatPow, p08VecAdd,
            p08_t3_matVec_id]
  | succ m ih =>
      intro i
      have hrec := p08_t3_residual_recurrence dimensionBounds run norm
        constants roundoff hcorr m i
      have hmono :
          p08MatVec (p08Lemma43Propagation constants)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i ≤
            p08MatVec (p08Lemma43Propagation constants)
              (p08Lemma43Bound constants m) i := by
        apply p08_t3_matVec_mono hP
        intro j
        simpa [p08AbsVec] using ih j
      calc
        |p08ExactResidualAfterCorrection run (Nat.succ m) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
                (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
              p08Lemma43RecurrenceForcing constants i := by
          simpa [Nat.succ_eq_add_one] using hrec
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
                (p08Lemma43Bound constants m) i +
              p08Lemma43RecurrenceForcing constants i := by linarith
        _ = p08Lemma43Bound constants (Nat.succ m) i := by
          simpa [Nat.succ_eq_add_one] using
            p08_t3_bound_succ dimensionBounds run norm constants m i

end HighamBench
