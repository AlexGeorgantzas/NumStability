import HighamBench.P08Definitions

namespace HighamBench

private lemma p08_matVec_add {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatAdd A B) x i =
      p08MatVec A x i + p08MatVec B x i := by
  simp [p08MatVec, p08MatAdd, Finset.sum_add_distrib, add_mul]

private lemma p08_matVec_scale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatScale a A) x i = a * p08MatVec A x i := by
  simp [p08MatVec, p08MatScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p08_matVec_id {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08IdMatrix n) x i = x i := by
  simp [p08MatVec, p08IdMatrix]

private lemma p08_matVec_mul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec (p08MatMul A B) x i =
      p08MatVec A (p08MatVec B x) i := by
  simp only [p08MatVec, p08MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma p08_matMul_assoc {n : ℕ}
    (A B C : Fin n → Fin n → ℝ) :
    p08MatMul (p08MatMul A B) C = p08MatMul A (p08MatMul B C) := by
  funext i j
  simp only [p08MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

private lemma p08_matVec_vecAdd {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecAdd x y) i =
      p08MatVec A x i + p08MatVec A y i := by
  simp [p08MatVec, p08VecAdd, Finset.sum_add_distrib, mul_add]

private lemma p08_matVec_vecScale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p08MatVec A (p08VecScale a x) i =
      a * p08MatVec A x i := by
  simp [p08MatVec, p08VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p08_matVec_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p08MatNonnegative A)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (i : Fin n) :
    0 ≤ p08MatVec A x i := by
  unfold p08MatVec
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p08_matMul_nonnegative {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) (hB : p08MatNonnegative B) :
    p08MatNonnegative (p08MatMul A B) := by
  intro i j
  unfold p08MatMul
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

private lemma p08_matScale_nonnegative {n : ℕ}
    {a : ℝ} (ha : 0 ≤ a) {A : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) :
    p08MatNonnegative (p08MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private lemma p08_absMatrix_nonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) : p08MatNonnegative (p08AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p08_matVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p08MatNonnegative A)
    {x y : Fin n → ℝ} (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p08MatVec A x i ≤ p08MatVec A y i := by
  unfold p08MatVec
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08_abs_matVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤
      p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  unfold p08MatVec p08AbsMatrix p08AbsVec
  calc
    |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := by simp only [abs_mul]

private lemma p08_residualUnitRoundoff_pos {n : ℕ}
    (run : P08IterativeRefinementRun n) :
    0 < p08ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp [p08ResidualUnitRoundoff, run.u_pos, pow_pos]

private lemma p08_lemma43_raw_algebra {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (z : Fin n → ℝ) (i : Fin n) :
    let ubar := p08ResidualUnitRoundoff run.precision run.u
    let alpha := n * ubar + p08Lemma43c3 run * run.u ^ 2
    let gamma := constants.c5 * ubar + run.u
    let absA := p08AbsMatrix run.A
    let absAinv := p08AbsMatrix run.Ainv
    let absx := p08AbsVec run.exactSolution
    (alpha * p08MatVec absA absx i + gamma * p08MatVec absA z i) +
        (run.u * p08MatVec (p08MatMul constants.C2 absA) z i +
          run.u *
            (alpha *
                p08MatVec
                  (p08MatMul constants.C2
                    (p08MatMul absA absAinv))
                  (p08MatVec absA absx) i +
              gamma *
                p08MatVec
                  (p08MatMul constants.C2
                    (p08MatMul absA absAinv))
                  (p08MatVec absA z) i)) =
      run.u *
          p08MatVec (p08MatMul constants.C6 absA) z i +
        alpha * p08MatVec absA absx i +
        ubar * run.u *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C7
                (p08MatMul absA absAinv)) absA)
            absx i := by
  dsimp only
  rw [constants.C6_definition, constants.C7_definition]
  simp only [p08_matVec_add, p08_matVec_scale, p08_matVec_mul,
    p08_matVec_id]
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  have hubar : p08ResidualUnitRoundoff run.precision run.u ≠ 0 :=
    ne_of_gt (p08_residualUnitRoundoff_pos run)
  field_simp
  ring

private lemma p08_exactResidual_eq_errors {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    p08ExactResidualAfterCorrection run m i =
      -roundoff.residualError m i - roundoff.correctionError m i := by
  have hr := congrFun (roundoff.residual_equation m) i
  have hc := congrFun (roundoff.correction_equation m) i
  unfold p08ExactResidualAfterCorrection
  simp only [p08VecSub, p08VecAdd] at hr hc ⊢
  unfold p08MatVec at hr hc ⊢
  simp only [p08VecSub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

private lemma p08_lemma43_raw_bound {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff : P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p08ExactResidualAfterCorrection run m i| ≤
      run.u *
          p08MatVec
            (p08MatMul constants.C6 (p08AbsMatrix run.A))
            (p08AbsVec
              (p08VecSub (run.iterate m) run.exactSolution)) i +
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
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  let alpha := n * ubar + p08Lemma43c3 run * run.u ^ 2
  let gamma := constants.c5 * ubar + run.u
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let e := p08VecSub (run.iterate m) run.exactSolution
  let X := p08MatVec absA absx
  let Z := p08MatVec absA (p08AbsVec e)
  let D := p08VecAdd (p08VecScale alpha X) (p08VecScale gamma Z)
  let M := p08MatMul constants.C2 (p08MatMul absA absAinv)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hkappa : 0 ≤ p08KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hfactor : 0 ≤ run.u * p08KappaInverse run norm :=
    mul_nonneg hu hkappa
  have hc1small :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    have h :
        constants.c1 * (run.u * p08KappaInverse run norm) ≤
          constants.c8 * (run.u * p08KappaInverse run norm) :=
      mul_le_mul_of_nonneg_right constants.c1_le_c8 hfactor
    calc
      constants.c1 * run.u * p08KappaInverse run norm =
          constants.c1 * (run.u * p08KappaInverse run norm) := by ring
      _ ≤ constants.c8 * (run.u * p08KappaInverse run norm) := h
      _ = constants.c8 * run.u * p08KappaInverse run norm := by ring
      _ ≤ 1 / 2 := hsmall
  have hM : p08MatNonnegative M := by
    exact p08_matMul_nonnegative constants.C2_nonnegative
      (p08_matMul_nonnegative (p08_absMatrix_nonnegative run.A)
        (p08_absMatrix_nonnegative run.Ainv))
  have hres : ∀ j, |roundoff.residualError m j| ≤ D j := by
    intro j
    calc
      |roundoff.residualError m j| ≤
          alpha * X j + constants.c5 * ubar * Z j +
            run.u * |p08MatVec run.A e j| := by
              simpa [alpha, X, Z, e, absA, absx, ubar] using
                roundoff.residual_error_bound m j
      _ ≤ alpha * X j + constants.c5 * ubar * Z j +
            run.u * Z j := by
              gcongr
              exact p08_abs_matVec_le run.A e j
      _ = D j := by
        simp [D, p08VecAdd, p08VecScale, gamma]
        ring
  have hMD :
      p08MatVec M D i =
        alpha * p08MatVec M X i + gamma * p08MatVec M Z i := by
    simp [D, p08_matVec_vecAdd, p08_matVec_vecScale]
  have hcorr :
      |roundoff.correctionError m i| ≤
        run.u *
            p08MatVec (p08MatMul constants.C2 absA) (p08AbsVec e) i +
          run.u *
            (alpha * p08MatVec M X i +
              gamma * p08MatVec M Z i) := by
    calc
      |roundoff.correctionError m i| ≤
          run.u *
              p08MatVec (p08MatMul constants.C2 absA) (p08AbsVec e) i +
            run.u * p08MatVec M (p08AbsVec (roundoff.residualError m)) i := by
              simpa [M, absA, absAinv, e, p08_matMul_assoc] using
                roundoff.correction_error_bound hc1small m i
      _ ≤ run.u *
              p08MatVec (p08MatMul constants.C2 absA) (p08AbsVec e) i +
            run.u * p08MatVec M D i := by
              gcongr
              exact p08_matVec_mono hM hres i
      _ = _ := by rw [hMD]
  rw [p08_exactResidual_eq_errors dimensionBounds run norm constants roundoff m i]
  calc
    |-roundoff.residualError m i - roundoff.correctionError m i| ≤
        |roundoff.residualError m i| +
          |roundoff.correctionError m i| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le (-roundoff.residualError m i)
                (-roundoff.correctionError m i))
    _ ≤ D i +
        (run.u *
            p08MatVec (p08MatMul constants.C2 absA) (p08AbsVec e) i +
          run.u *
            (alpha * p08MatVec M X i +
              gamma * p08MatVec M Z i)) := add_le_add (hres i) hcorr
    _ = run.u *
          p08MatVec (p08MatMul constants.C6 absA) (p08AbsVec e) i +
        alpha * p08MatVec absA absx i +
        ubar * run.u *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C7 (p08MatMul absA absAinv)) absA)
            absx i := by
              simpa [D, p08VecAdd, p08VecScale, X, Z, M] using
                p08_lemma43_raw_algebra dimensionBounds run norm constants
                  (p08AbsVec e) i
    _ = _ := by rfl

private lemma p08_lemma43_initial_algebra {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    run.u *
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
            (p08AbsVec run.exactSolution) i =
      p08Lemma43InitialVector constants i := by
  simp only [p08Lemma43InitialVector, p08VecScale]
  rw [constants.C10_definition]
  simp only [p08_matVec_mul,
    p08_matVec_add, p08_matVec_scale, p08_matVec_id]
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  field_simp

private lemma p08_lemma43_stationary_nonnegative {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    0 ≤ p08Lemma43StationaryVector constants i := by
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p08ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p08_residualUnitRoundoff_pos run)
  have hAbsA := p08_absMatrix_nonnegative run.A
  have hAbsAinv := p08_absMatrix_nonnegative run.Ainv
  have hx : ∀ j, 0 ≤ p08AbsVec run.exactSolution j := fun j ↦ abs_nonneg _
  have h1 :
      0 ≤ p08MatVec (p08AbsMatrix run.A)
        (p08AbsVec run.exactSolution) i :=
    p08_matVec_nonnegative hAbsA hx i
  have h2 :
      0 ≤ p08MatVec
        (p08MatMul constants.C11 (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i :=
    p08_matVec_nonnegative
      (p08_matMul_nonnegative constants.C11_nonnegative hAbsA) hx i
  have h3 :
      0 ≤ p08MatVec
        (p08MatMul
          (p08MatMul constants.C12
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
          (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i :=
    p08_matVec_nonnegative
      (p08_matMul_nonnegative
        (p08_matMul_nonnegative constants.C12_nonnegative
          (p08_matMul_nonnegative hAbsA hAbsAinv)) hAbsA) hx i
  simp only [p08Lemma43StationaryVector, p08VecAdd, p08VecScale]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hubar) h1)
    (add_nonneg (mul_nonneg (sq_nonneg _) h2)
      (mul_nonneg (mul_nonneg hubar hu) h3))

private lemma p08_exactResidual_vector_eq {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) :
    p08ExactResidualAfterCorrection run m =
      p08MatVec run.A
        (p08VecSub
          (p08VecSub (run.iterate m) (run.correction m))
          run.exactSolution) := by
  funext i
  have hexact := congrFun run.exact_system i
  unfold p08ExactResidualAfterCorrection
  simp only [p08VecSub]
  unfold p08MatVec at hexact ⊢
  simp only [p08VecSub]
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  linarith

private lemma p08_preupdate_identity {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    run.iterate m i - run.correction m i =
      run.exactSolution i +
        p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i := by
  have hinv :
      p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i =
        p08VecSub
          (p08VecSub (run.iterate m) (run.correction m))
          run.exactSolution i := by
    rw [p08_exactResidual_vector_eq run m]
    rw [← p08_matVec_mul, run.inverse_left]
    exact p08_matVec_id _ i
  rw [hinv]
  simp [p08VecSub]

private lemma p08_update_error_vector_bound {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |p08VecSub (run.iterate (m + 1)) run.exactSolution i| ≤
      (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u * |run.exactSolution i| := by
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hupdate := run.update_error_bound m i
  have hpre :
      |run.iterate m i - run.correction m i| ≤
        |run.exactSolution i| +
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
    rw [p08_preupdate_identity run m i]
    calc
      |run.exactSolution i +
          p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i| ≤
          |run.exactSolution i| +
            |p08MatVec run.Ainv
              (p08ExactResidualAfterCorrection run m) i| := abs_add_le _ _
      _ ≤ |run.exactSolution i| +
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
              gcongr
              exact p08_abs_matVec_le run.Ainv
                (p08ExactResidualAfterCorrection run m) i
  have hupdate' :
      |run.updateError (m + 1) i| ≤
        run.u *
          (|run.exactSolution i| +
            p08MatVec (p08AbsMatrix run.Ainv)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i) :=
    hupdate.trans (mul_le_mul_of_nonneg_left hpre hu)
  have heq := congrFun (run.update_equation m) i
  simp only [p08VecAdd, p08VecSub] at heq
  simp only [p08VecSub]
  rw [heq]
  calc
    |run.iterate m i - run.correction m i +
          run.updateError (m + 1) i - run.exactSolution i| =
        |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i +
          run.updateError (m + 1) i| := by
            rw [p08_preupdate_identity run m i]
            ring_nf
    _ ≤ |p08MatVec run.Ainv
          (p08ExactResidualAfterCorrection run m) i| +
        |run.updateError (m + 1) i| := abs_add_le _ _
    _ ≤ p08MatVec (p08AbsMatrix run.Ainv)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u *
          (|run.exactSolution i| +
            p08MatVec (p08AbsMatrix run.Ainv)
              (p08AbsVec (p08ExactResidualAfterCorrection run m)) i) :=
      add_le_add (p08_abs_matVec_le run.Ainv
        (p08ExactResidualAfterCorrection run m) i) hupdate'
    _ = (1 + run.u) *
          p08MatVec (p08AbsMatrix run.Ainv)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u * |run.exactSolution i| := by ring

private lemma p08_lemma43_recurrence_algebra {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (q : Fin n → ℝ) (i : Fin n) :
    run.u *
          p08MatVec
            (p08MatMul constants.C6 (p08AbsMatrix run.A))
            (p08VecAdd
              (p08VecScale (1 + run.u)
                (p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q)))
              (p08VecScale run.u (p08AbsVec run.exactSolution))) i +
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
            (p08AbsVec run.exactSolution) i =
      p08MatVec (p08Lemma43Propagation constants) (p08AbsVec q) i +
        p08Lemma43RecurrenceForcing constants i := by
  simp only [p08Lemma43Propagation, p08Lemma43RecurrenceForcing]
  rw [constants.C8_definition, constants.C9_definition]
  simp only [p08VecAdd, p08VecScale, p08_matVec_vecAdd, p08_matVec_vecScale,
    p08_matVec_scale, p08_matVec_add, p08_matVec_id]
  simp_rw [p08_matVec_mul]
  simp only [p08_matVec_scale, p08_matVec_add, p08_matVec_id]
  have hq :
      p08MatVec
          (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))
          (p08AbsVec q) =
        p08MatVec (p08AbsMatrix run.A)
          (p08MatVec (p08AbsMatrix run.Ainv) (p08AbsVec q)) := by
    funext j
    exact p08_matVec_mul _ _ _ j
  rw [hq]
  ring

private lemma p08_lemma43_recurrence {n : ℕ}
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
  let N := p08MatMul constants.C6 (p08AbsMatrix run.A)
  let Y := p08VecAdd
    (p08VecScale (1 + run.u)
      (p08MatVec (p08AbsMatrix run.Ainv)
        (p08AbsVec (p08ExactResidualAfterCorrection run m))))
    (p08VecScale run.u (p08AbsVec run.exactSolution))
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hN : p08MatNonnegative N :=
    p08_matMul_nonnegative constants.C6_nonnegative
      (p08_absMatrix_nonnegative run.A)
  have he : ∀ j,
      p08AbsVec
          (p08VecSub (run.iterate (m + 1)) run.exactSolution) j ≤
        Y j := by
    intro j
    simpa [p08AbsVec, Y, p08VecAdd, p08VecScale] using
      p08_update_error_vector_bound run m j
  calc
    |p08ExactResidualAfterCorrection run (m + 1) i| ≤
        run.u * p08MatVec N
              (p08AbsVec
                (p08VecSub (run.iterate (m + 1)) run.exactSolution)) i +
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
                simpa [N] using p08_lemma43_raw_bound dimensionBounds run norm
                  constants roundoff hsmall (m + 1) i
    _ ≤ run.u * p08MatVec N Y i +
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
                gcongr
                exact p08_matVec_mono hN he i
    _ = _ := by
      simpa [N, Y] using
        p08_lemma43_recurrence_algebra dimensionBounds run norm constants
          (p08ExactResidualAfterCorrection run m) i

private lemma p08_C11_action_fixed {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08MatVec
        (p08MatMul constants.C11 (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i =
      p08MatVec
          (p08MatMul constants.C9 (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) i +
        p08MatVec (p08Lemma43Propagation constants)
          (p08MatVec
            (p08MatMul constants.C11 (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution)) i := by
  let v := p08MatVec
    (p08MatMul constants.C11 (p08AbsMatrix run.A))
    (p08AbsVec run.exactSolution)
  change p08MatVec
      (p08MatMul constants.C11 (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution) i =
    p08MatVec (p08MatMul constants.C9 (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i +
      p08MatVec (p08Lemma43Propagation constants) v i
  rw [constants.C11_fixed_point]
  simp only [p08_matVec_add, p08Lemma43Propagation, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  unfold v
  simp only [p08_matVec_add, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  simp only [p08_matVec_scale]
  simp only [p08_matVec_mul]
  have h11 :
      p08MatVec (p08MatMul constants.C11 (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) =
        p08MatVec constants.C11
          (p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution)) := by
    funext j
    exact p08_matVec_mul _ _ _ j
  rw [h11]

private lemma p08_C12_action_fixed {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08MatVec
        (p08MatMul
          (p08MatMul constants.C12
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
          (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i =
      n *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C8
                (p08MatMul (p08AbsMatrix run.A)
                  (p08AbsMatrix run.Ainv)))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i +
        p08MatVec
            (p08MatMul
              (p08MatMul constants.C7
                (p08MatMul (p08AbsMatrix run.A)
                  (p08AbsMatrix run.Ainv)))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution) i +
        p08MatVec (p08Lemma43Propagation constants)
          (p08MatVec
            (p08MatMul
              (p08MatMul constants.C12
                (p08MatMul (p08AbsMatrix run.A)
                  (p08AbsMatrix run.Ainv)))
              (p08AbsMatrix run.A))
            (p08AbsVec run.exactSolution)) i := by
  let v := p08MatVec
    (p08MatMul
      (p08MatMul constants.C12
        (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
      (p08AbsMatrix run.A))
    (p08AbsVec run.exactSolution)
  change p08MatVec
      (p08MatMul
        (p08MatMul constants.C12
          (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
        (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution) i =
    n * p08MatVec
        (p08MatMul
          (p08MatMul constants.C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
          (p08AbsMatrix run.A))
        (p08AbsVec run.exactSolution) i +
      p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) i +
      p08MatVec (p08Lemma43Propagation constants) v i
  rw [constants.C12_fixed_point]
  simp only [p08_matVec_add, p08Lemma43Propagation, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  unfold v
  simp only [p08_matVec_add, p08_matVec_scale]
  simp_rw [p08_matVec_mul]
  simp only [p08_matVec_scale]
  simp only [p08_matVec_mul]
  have h12 :
      p08MatVec
          (p08MatMul
            (p08MatMul constants.C12
              (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) =
        p08MatVec constants.C12
          (p08MatVec
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))
            (p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec run.exactSolution))) := by
    funext j
    calc
      p08MatVec
          (p08MatMul
            (p08MatMul constants.C12
              (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
            (p08AbsMatrix run.A))
          (p08AbsVec run.exactSolution) j =
        p08MatVec
          (p08MatMul constants.C12
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))
          (p08MatVec (p08AbsMatrix run.A)
            (p08AbsVec run.exactSolution)) j := p08_matVec_mul _ _ _ j
      _ = _ := p08_matVec_mul _ _ _ j
  rw [h12]

private lemma p08_lemma43_stationary_fixed {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43StationaryVector constants) i +
        p08Lemma43RecurrenceForcing constants i =
      p08Lemma43StationaryVector constants i := by
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  have h11 := p08_C11_action_fixed dimensionBounds run norm constants i
  have h12 := p08_C12_action_fixed dimensionBounds run norm constants i
  have hpA :
      p08MatVec (p08Lemma43Propagation constants)
          (p08MatVec absA absx) i =
        run.u *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C8 (p08MatMul absA absAinv)) absA)
            absx i := by
    simp only [p08Lemma43Propagation, p08_matVec_scale]
    simp_rw [p08_matVec_mul]
    rfl
  simp only [p08Lemma43StationaryVector, p08Lemma43RecurrenceForcing]
  simp only [p08_matVec_vecAdd, p08_matVec_vecScale,
    p08VecAdd, p08VecScale]
  change
    (n * ubar) *
          p08MatVec (p08Lemma43Propagation constants)
            (p08MatVec absA absx) i +
        (run.u ^ 2 *
            p08MatVec (p08Lemma43Propagation constants)
              (p08MatVec (p08MatMul constants.C11 absA) absx) i +
          (ubar * run.u) *
            p08MatVec (p08Lemma43Propagation constants)
              (p08MatVec
                (p08MatMul
                  (p08MatMul constants.C12 (p08MatMul absA absAinv))
                  absA) absx) i) +
      ((n * ubar) * p08MatVec absA absx i +
        (run.u ^ 2 *
            p08MatVec (p08MatMul constants.C9 absA) absx i +
          (ubar * run.u) *
            p08MatVec
              (p08MatMul
                (p08MatMul constants.C7 (p08MatMul absA absAinv)) absA)
              absx i)) =
    (n * ubar) * p08MatVec absA absx i +
      (run.u ^ 2 *
          p08MatVec (p08MatMul constants.C11 absA) absx i +
        (ubar * run.u) *
          p08MatVec
            (p08MatMul
              (p08MatMul constants.C12 (p08MatMul absA absAinv)) absA)
            absx i)
  rw [hpA]
  dsimp only [ubar, absA, absAinv, absx] at h11 h12 ⊢
  linear_combination
    -(run.u ^ 2) * h11 -
      (p08ResidualUnitRoundoff run.precision run.u * run.u) * h12

private lemma p08_lemma43_bound_step {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (m : ℕ) (i : Fin n) :
    p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43Bound constants m) i +
        p08Lemma43RecurrenceForcing constants i =
      p08Lemma43Bound constants (m + 1) i := by
  simp only [p08Lemma43Bound, p08VecAdd, p08_matVec_vecAdd]
  rw [add_assoc]
  rw [p08_lemma43_stationary_fixed dimensionBounds run norm constants i]
  simp only [p08MatPow, p08_matVec_mul]

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
      have he0 :
          p08AbsVec
              (p08VecSub (run.iterate 0) run.exactSolution) =
            p08AbsVec run.exactSolution := by
        funext j
        simp only [p08AbsVec, p08VecSub]
        rw [congrFun run.iterate_zero j]
        simp
      have hbase :
          |p08ExactResidualAfterCorrection run 0 i| ≤
            p08Lemma43InitialVector constants i := by
        calc
          |p08ExactResidualAfterCorrection run 0 i| ≤
              run.u *
                  p08MatVec
                    (p08MatMul constants.C6 (p08AbsMatrix run.A))
                    (p08AbsVec
                      (p08VecSub (run.iterate 0) run.exactSolution)) i +
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
                    (p08AbsVec run.exactSolution) i :=
            p08_lemma43_raw_bound dimensionBounds run norm constants roundoff
              hsmall 0 i
          _ = p08Lemma43InitialVector constants i := by
            rw [he0]
            exact p08_lemma43_initial_algebra dimensionBounds run norm constants i
      calc
        |p08ExactResidualAfterCorrection run 0 i| ≤
            p08Lemma43InitialVector constants i := hbase
        _ ≤ p08Lemma43InitialVector constants i +
            p08Lemma43StationaryVector constants i :=
          le_add_of_nonneg_right
            (p08_lemma43_stationary_nonnegative dimensionBounds run norm
              constants i)
        _ = p08Lemma43Bound constants 0 i := by
          simp [p08Lemma43Bound, p08MatPow, p08VecAdd, p08_matVec_id]
  | succ m ih =>
      intro i
      have hu : 0 ≤ run.u := le_of_lt run.u_pos
      have hP :
          p08MatNonnegative (p08Lemma43Propagation constants) := by
        unfold p08Lemma43Propagation
        exact p08_matScale_nonnegative hu
          (p08_matMul_nonnegative constants.C8_nonnegative
            (p08_matMul_nonnegative (p08_absMatrix_nonnegative run.A)
              (p08_absMatrix_nonnegative run.Ainv)))
      calc
        |p08ExactResidualAfterCorrection run (Nat.succ m) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
                (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
              p08Lemma43RecurrenceForcing constants i := by
                simpa [Nat.succ_eq_add_one] using
                  p08_lemma43_recurrence dimensionBounds run norm constants
                    roundoff hsmall m i
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
                (p08Lemma43Bound constants m) i +
              p08Lemma43RecurrenceForcing constants i := by
                have hmono :
                    p08MatVec (p08Lemma43Propagation constants)
                        (p08AbsVec
                          (p08ExactResidualAfterCorrection run m)) i ≤
                      p08MatVec (p08Lemma43Propagation constants)
                        (p08Lemma43Bound constants m) i :=
                  p08_matVec_mono hP
                    (fun j ↦ by simpa [p08AbsVec] using ih j) i
                exact add_le_add_left hmono _
        _ = p08Lemma43Bound constants (Nat.succ m) i := by
          simpa [Nat.succ_eq_add_one] using
            p08_lemma43_bound_step dimensionBounds run norm constants m i

end HighamBench
