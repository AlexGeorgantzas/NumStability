import HighamBench.P08Definitions

namespace HighamBench

private lemma p08MatVec_add {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecAdd x y) =
      p08VecAdd (p08MatVec A x) (p08MatVec A y) := by
  funext i
  simp [p08MatVec, p08VecAdd, mul_add, Finset.sum_add_distrib]

private lemma p08MatVec_sub {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    p08MatVec A (p08VecSub x y) =
      p08VecSub (p08MatVec A x) (p08MatVec A y) := by
  funext i
  simp [p08MatVec, p08VecSub, mul_sub, Finset.sum_sub_distrib]

private lemma p08MatVec_scale {n : ℕ}
    (A : Fin n → Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) :
    p08MatVec A (p08VecScale a x) =
      p08VecScale a (p08MatVec A x) := by
  funext i
  simp [p08MatVec, p08VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p08MatVec_matAdd {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatAdd A B) x =
      p08VecAdd (p08MatVec A x) (p08MatVec B x) := by
  funext i
  simp [p08MatVec, p08MatAdd, p08VecAdd, add_mul,
    Finset.sum_add_distrib]

private lemma p08MatVec_matScale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatScale a A) x =
      p08VecScale a (p08MatVec A x) := by
  funext i
  simp [p08MatVec, p08MatScale, p08VecScale, Finset.mul_sum]
  ring

private lemma p08MatVec_matMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    p08MatVec (p08MatMul A B) x = p08MatVec A (p08MatVec B x) := by
  funext i
  simp only [p08MatVec, p08MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  congr 1
  funext k
  ring

private lemma p08MatVec_id {n : ℕ} (x : Fin n → ℝ) :
    p08MatVec (p08IdMatrix n) x = x := by
  funext i
  simp [p08MatVec, p08IdMatrix]

private lemma p08MatVec_nonnegative {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ p08MatVec A x i := by
  intro i
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p08MatVec_mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x y : Fin n → ℝ}
    (hA : p08MatNonnegative A) (hxy : ∀ i, x i ≤ y i) :
    ∀ i, p08MatVec A x i ≤ p08MatVec A y i := by
  intro i
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p08AbsMatVec_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |p08MatVec A x i| ≤
      p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
  calc
    |p08MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = p08MatVec (p08AbsMatrix A) (p08AbsVec x) i := by
      simp [p08MatVec, p08AbsMatrix, p08AbsVec, abs_mul]

private lemma p08AbsMatrix_nonnegative {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    p08MatNonnegative (p08AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p08MatMul_nonnegative {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p08MatNonnegative A) (hB : p08MatNonnegative B) :
    p08MatNonnegative (p08MatMul A B) := by
  intro i j
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

private lemma p08MatScale_nonnegative {n : ℕ}
    {a : ℝ} {A : Fin n → Fin n → ℝ}
    (ha : 0 ≤ a) (hA : p08MatNonnegative A) :
    p08MatNonnegative (p08MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private lemma p08VecScale_nonnegative {n : ℕ}
    {a : ℝ} {x : Fin n → ℝ}
    (ha : 0 ≤ a) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ p08VecScale a x i := by
  intro i
  exact mul_nonneg ha (hx i)

private lemma p08KappaInverse_nonnegative {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n) :
    0 ≤ p08KappaInverse run norm := by
  exact norm.matrix_norm_nonnegative _

private lemma p08Inverse_action {n : ℕ}
    (run : P08IterativeRefinementRun n) (x : Fin n → ℝ) :
    p08MatVec run.Ainv (p08MatVec run.A x) = x := by
  rw [← p08MatVec_matMul, run.inverse_left, p08MatVec_id]

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
    p08KappaInverse_nonnegative run norm
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hcsmall :
      constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 := by
    have hprod :
        0 ≤ (constants.c8 - constants.c1) * run.u *
          p08KappaInverse run norm :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr constants.c1_le_c8) hu) hkappa
    nlinarith
  have hqeq : ∀ m i,
      p08ExactResidualAfterCorrection run m i =
        -roundoff.residualError m i - roundoff.correctionError m i := by
    intro m i
    have hr := congrFun (roundoff.residual_equation m) i
    have hc := congrFun (roundoff.correction_equation m) i
    simp only [p08ExactResidualAfterCorrection] at ⊢
    rw [p08MatVec_sub] at ⊢
    simp only [p08VecSub, p08VecAdd] at hr hc ⊢
    linarith
  let absA : Fin n → Fin n → ℝ := p08AbsMatrix run.A
  let absAinv : Fin n → Fin n → ℝ := p08AbsMatrix run.Ainv
  let absx : Fin n → ℝ := p08AbsVec run.exactSolution
  let ubar : ℝ := p08ResidualUnitRoundoff run.precision run.u
  let err : ℕ → Fin n → ℝ := fun m ↦
    p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)
  let residualMajorant : ℕ → Fin n → ℝ := fun m ↦
    p08VecAdd
      (p08VecScale
        (n * ubar + p08Lemma43c3 run * run.u ^ 2)
        (p08MatVec absA absx))
      (p08VecAdd
        (p08VecScale (constants.c5 * ubar) (p08MatVec absA (err m)))
        (p08VecScale run.u (p08MatVec absA (err m))))
  have hubar : 0 < ubar := by
    cases hp : run.precision <;>
      simp [ubar, p08ResidualUnitRoundoff, hp, run.u_pos,
        pow_pos] 
  have hubar0 : p08ResidualUnitRoundoff run.precision run.u ≠ 0 := by
    exact ne_of_gt hubar
  have hf : ∀ m i,
      |roundoff.residualError m i| ≤ residualMajorant m i := by
    intro m i
    have h := roundoff.residual_error_bound m i
    have hae := p08AbsMatVec_le run.A
      (p08VecSub (run.iterate m) run.exactSolution) i
    dsimp only [residualMajorant, p08VecAdd, p08VecScale]
    change
      |roundoff.residualError m i| ≤
        (n * ubar + p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec absA absx i +
          (constants.c5 * ubar * p08MatVec absA (err m) i +
            run.u * p08MatVec absA (err m) i)
    dsimp only [ubar, absA, absx, err]
    calc
      |roundoff.residualError m i| ≤
          (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec run.exactSolution) i +
          constants.c5 * p08ResidualUnitRoundoff run.precision run.u *
            p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec
                (p08VecSub (run.iterate m) run.exactSolution)) i +
          run.u *
            |p08MatVec run.A
              (p08VecSub (run.iterate m) run.exactSolution) i| := h
      _ ≤
          (n * p08ResidualUnitRoundoff run.precision run.u +
              p08Lemma43c3 run * run.u ^ 2) *
            p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec run.exactSolution) i +
          (constants.c5 * p08ResidualUnitRoundoff run.precision run.u *
              p08MatVec (p08AbsMatrix run.A)
                (p08AbsVec
                  (p08VecSub (run.iterate m) run.exactSolution)) i +
            run.u * p08MatVec (p08AbsMatrix run.A)
              (p08AbsVec
                (p08VecSub (run.iterate m) run.exactSolution)) i) := by
        have hlast := mul_le_mul_of_nonneg_left hae hu
        linarith
  have hpre : ∀ m i,
      |p08ExactResidualAfterCorrection run m i| ≤
        residualMajorant m i +
          run.u * p08MatVec constants.C2 (p08MatVec absA (err m)) i +
          run.u * p08MatVec constants.C2
            (p08MatVec absA
              (p08MatVec absAinv (residualMajorant m))) i := by
    intro m i
    have hg := roundoff.correction_error_bound hcsmall m i
    have hMnonneg : p08MatNonnegative
        (p08MatMul
          (p08MatMul constants.C2 (p08AbsMatrix run.A))
          (p08AbsMatrix run.Ainv)) :=
      p08MatMul_nonnegative
        (p08MatMul_nonnegative constants.C2_nonnegative
          (p08AbsMatrix_nonnegative run.A))
        (p08AbsMatrix_nonnegative run.Ainv)
    have hmono := p08MatVec_mono hMnonneg (hf m)
    simp_rw [p08MatVec_matMul] at hg hmono
    rw [hqeq m i]
    calc
      |-roundoff.residualError m i - roundoff.correctionError m i| ≤
          |roundoff.residualError m i| +
            |roundoff.correctionError m i| := by
        simpa [sub_eq_add_neg, abs_neg] using
          (abs_add_le (-roundoff.residualError m i)
            (-roundoff.correctionError m i))
      _ ≤ residualMajorant m i +
          (run.u * p08MatVec constants.C2
              (p08MatVec (p08AbsMatrix run.A)
                (p08AbsVec
                  (p08VecSub (run.iterate m) run.exactSolution))) i +
            run.u * p08MatVec constants.C2
              (p08MatVec (p08AbsMatrix run.A)
                (p08MatVec (p08AbsMatrix run.Ainv)
                  (p08AbsVec (roundoff.residualError m)))) i) :=
        add_le_add (hf m i) hg
      _ ≤ residualMajorant m i +
          run.u * p08MatVec constants.C2 (p08MatVec absA (err m)) i +
          run.u * p08MatVec constants.C2
            (p08MatVec absA
              (p08MatVec absAinv (residualMajorant m))) i := by
        have hmul := mul_le_mul_of_nonneg_left (hmono i) hu
        change run.u * p08MatVec constants.C2
            (p08MatVec (p08AbsMatrix run.A)
              (p08MatVec (p08AbsMatrix run.Ainv)
                (p08AbsVec (roundoff.residualError m)))) i ≤
          run.u * p08MatVec constants.C2
            (p08MatVec (p08AbsMatrix run.A)
              (p08MatVec (p08AbsMatrix run.Ainv)
                (residualMajorant m))) i at hmul
        dsimp only [absA, absAinv, err]
        linarith
  have hraw : ∀ m i,
      |p08ExactResidualAfterCorrection run m i| ≤
        run.u * p08MatVec constants.C6 (p08MatVec absA (err m)) i +
        n * ubar * p08MatVec absA absx i +
        run.u ^ 2 * p08Lemma43c3 run * p08MatVec absA absx i +
        ubar * run.u * p08MatVec constants.C7
          (p08MatVec absA
            (p08MatVec absAinv (p08MatVec absA absx))) i := by
    intro m i
    calc
      |p08ExactResidualAfterCorrection run m i| ≤
          residualMajorant m i +
            run.u * p08MatVec constants.C2 (p08MatVec absA (err m)) i +
            run.u * p08MatVec constants.C2
              (p08MatVec absA
                (p08MatVec absAinv (residualMajorant m))) i := hpre m i
      _ = run.u * p08MatVec constants.C6 (p08MatVec absA (err m)) i +
          n * ubar * p08MatVec absA absx i +
          run.u ^ 2 * p08Lemma43c3 run * p08MatVec absA absx i +
          ubar * run.u * p08MatVec constants.C7
            (p08MatVec absA
              (p08MatVec absAinv (p08MatVec absA absx))) i := by
        rw [constants.C6_definition, constants.C7_definition]
        dsimp only [residualMajorant]
        simp only [p08MatVec_add, p08MatVec_scale,
          p08MatVec_matAdd, p08MatVec_matScale,
          p08MatVec_matMul, p08MatVec_id]
        dsimp only [p08VecAdd, p08VecScale, absA, absAinv, absx, err, ubar]
        field_simp [ne_of_gt run.u_pos, hubar0]
        ring
  have hqvec : ∀ m,
      p08ExactResidualAfterCorrection run m =
        p08MatVec run.A
          (p08VecSub
            (p08VecSub (run.iterate m) (run.correction m))
            run.exactSolution) := by
    intro m
    funext i
    simp only [p08ExactResidualAfterCorrection]
    simp only [p08MatVec_sub]
    have hs := congrFun run.exact_system i
    dsimp only [p08VecSub] at hs ⊢
    linarith
  have hy : ∀ m,
      p08VecSub
          (p08VecSub (run.iterate m) (run.correction m))
          run.exactSolution =
        p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) := by
    intro m
    rw [hqvec m, p08Inverse_action]
  have herr : ∀ m i,
      err (m + 1) i ≤
        (1 + run.u) * p08MatVec absAinv
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        run.u * absx i := by
    intro m i
    have hupd := run.update_error_bound m i
    have hAi := p08AbsMatVec_le run.Ainv
      (p08ExactResidualAfterCorrection run m) i
    have hyi := congrFun (hy m) i
    have hupdate := congrFun (run.update_equation m) i
    have hnext :
        p08VecSub (run.iterate (m + 1)) run.exactSolution i =
          p08MatVec run.Ainv
              (p08ExactResidualAfterCorrection run m) i +
            run.updateError (m + 1) i := by
      dsimp only [p08VecSub, p08VecAdd] at hyi hupdate ⊢
      linarith
    have hyabs :
        |run.iterate m i - run.correction m i| ≤
          absx i + p08MatVec absAinv
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i := by
      dsimp only [p08VecSub] at hyi
      dsimp only [absx, absAinv, p08AbsVec]
      calc
        |run.iterate m i - run.correction m i| =
            |run.exactSolution i +
              p08MatVec run.Ainv
                (p08ExactResidualAfterCorrection run m) i| := by
          congr 1
          linarith
        _ ≤ |run.exactSolution i| +
            |p08MatVec run.Ainv
              (p08ExactResidualAfterCorrection run m) i| := abs_add_le _ _
        _ ≤ |run.exactSolution i| +
            p08MatVec (p08AbsMatrix run.Ainv)
              (p08AbsVec
                (p08ExactResidualAfterCorrection run m)) i := by
          gcongr
    dsimp only [err, p08AbsVec]
    rw [hnext]
    calc
      |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i +
          run.updateError (m + 1) i| ≤
        |p08MatVec run.Ainv (p08ExactResidualAfterCorrection run m) i| +
          |run.updateError (m + 1) i| := abs_add_le _ _
      _ ≤ p08MatVec absAinv
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
          run.u * (absx i + p08MatVec absAinv
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i) := by
        apply add_le_add hAi
        exact hupd.trans (mul_le_mul_of_nonneg_left hyabs hu)
      _ = (1 + run.u) * p08MatVec absAinv
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
          run.u * absx i := by ring
  have hrec : ∀ m i,
      |p08ExactResidualAfterCorrection run (m + 1) i| ≤
        p08MatVec (p08Lemma43Propagation constants)
          (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
        p08Lemma43RecurrenceForcing constants i := by
    intro m i
    have hCA : p08MatNonnegative (p08MatMul constants.C6 absA) :=
      p08MatMul_nonnegative constants.C6_nonnegative
        (p08AbsMatrix_nonnegative run.A)
    have hm : ∀ i,
        p08MatVec (p08MatMul constants.C6 absA) (err (m + 1)) i ≤
          p08MatVec (p08MatMul constants.C6 absA)
            (p08VecAdd
              (p08VecScale (1 + run.u)
                (p08MatVec absAinv
                  (p08AbsVec (p08ExactResidualAfterCorrection run m))))
              (p08VecScale run.u absx)) i := by
      apply p08MatVec_mono hCA
      intro j
      exact herr m j
    simp_rw [p08MatVec_matMul] at hm
    have hmul := mul_le_mul_of_nonneg_left (hm i) hu
    calc
      |p08ExactResidualAfterCorrection run (m + 1) i| ≤
          run.u * p08MatVec constants.C6
              (p08MatVec absA (err (m + 1))) i +
            n * ubar * p08MatVec absA absx i +
            run.u ^ 2 * p08Lemma43c3 run * p08MatVec absA absx i +
            ubar * run.u * p08MatVec constants.C7
              (p08MatVec absA
                (p08MatVec absAinv (p08MatVec absA absx))) i :=
        hraw (m + 1) i
      _ ≤ run.u * p08MatVec constants.C6
              (p08MatVec absA
                (p08VecAdd
                  (p08VecScale (1 + run.u)
                    (p08MatVec absAinv
                      (p08AbsVec
                        (p08ExactResidualAfterCorrection run m))))
                  (p08VecScale run.u absx))) i +
            n * ubar * p08MatVec absA absx i +
            run.u ^ 2 * p08Lemma43c3 run * p08MatVec absA absx i +
            ubar * run.u * p08MatVec constants.C7
              (p08MatVec absA
                (p08MatVec absAinv (p08MatVec absA absx))) i := by
        linarith
      _ = p08MatVec (p08Lemma43Propagation constants)
            (p08AbsVec (p08ExactResidualAfterCorrection run m)) i +
          p08Lemma43RecurrenceForcing constants i := by
        simp only [p08Lemma43Propagation,
          p08Lemma43RecurrenceForcing]
        rw [constants.C8_definition, constants.C9_definition]
        simp only [p08MatVec_add, p08MatVec_scale,
          p08MatVec_matAdd, p08MatVec_matScale,
          p08MatVec_matMul, p08MatVec_id]
        dsimp only [p08VecAdd, p08VecScale, absA, absAinv, absx, ubar]
        ring
  have herr0 : err 0 = absx := by
    funext i
    dsimp only [err]
    rw [run.iterate_zero]
    simp [absx, p08AbsVec, p08VecSub]
  have hbase : ∀ i,
      |p08ExactResidualAfterCorrection run 0 i| ≤
        p08Lemma43InitialVector constants i := by
    intro i
    calc
      |p08ExactResidualAfterCorrection run 0 i| ≤
          run.u * p08MatVec constants.C6
              (p08MatVec absA (err 0)) i +
            n * ubar * p08MatVec absA absx i +
            run.u ^ 2 * p08Lemma43c3 run * p08MatVec absA absx i +
            ubar * run.u * p08MatVec constants.C7
              (p08MatVec absA
                (p08MatVec absAinv (p08MatVec absA absx))) i := hraw 0 i
      _ = p08Lemma43InitialVector constants i := by
        rw [herr0]
        simp only [p08Lemma43InitialVector]
        rw [constants.C10_definition]
        simp only [p08MatVec_add, p08MatVec_scale,
          p08MatVec_matAdd, p08MatVec_matScale,
          p08MatVec_matMul, p08MatVec_id]
        dsimp only [p08VecAdd, p08VecScale, absA, absAinv, absx, ubar]
        field_simp [ne_of_gt run.u_pos]
        ring
  have hprop_nonnegative :
      p08MatNonnegative (p08Lemma43Propagation constants) := by
    exact p08MatScale_nonnegative hu
      (p08MatMul_nonnegative constants.C8_nonnegative
        (p08MatMul_nonnegative (p08AbsMatrix_nonnegative run.A)
          (p08AbsMatrix_nonnegative run.Ainv)))
  have hstation_nonnegative : ∀ i,
      0 ≤ p08Lemma43StationaryVector constants i := by
    have hx : ∀ i, 0 ≤ absx i := by
      intro i
      exact abs_nonneg _
    have hAx : ∀ i, 0 ≤ p08MatVec absA absx i :=
      p08MatVec_nonnegative (p08AbsMatrix_nonnegative run.A) hx
    have hC11Ax : ∀ i,
        0 ≤ p08MatVec constants.C11 (p08MatVec absA absx) i :=
      p08MatVec_nonnegative constants.C11_nonnegative hAx
    have hAiAx : ∀ i,
        0 ≤ p08MatVec absAinv (p08MatVec absA absx) i :=
      p08MatVec_nonnegative (p08AbsMatrix_nonnegative run.Ainv) hAx
    have hAAiAx : ∀ i,
        0 ≤ p08MatVec absA (p08MatVec absAinv
          (p08MatVec absA absx)) i :=
      p08MatVec_nonnegative (p08AbsMatrix_nonnegative run.A) hAiAx
    have hC12 : ∀ i,
        0 ≤ p08MatVec constants.C12
          (p08MatVec absA (p08MatVec absAinv
            (p08MatVec absA absx))) i :=
      p08MatVec_nonnegative constants.C12_nonnegative hAAiAx
    intro i
    simp only [p08Lemma43StationaryVector]
    simp only [p08MatVec_matMul]
    dsimp only [p08VecAdd, p08VecScale]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hub : 0 ≤ ubar :=
      le_of_lt hubar
    have h1 := mul_nonneg (mul_nonneg hn hub) (hAx i)
    have h2 := mul_nonneg (sq_nonneg run.u) (hC11Ax i)
    have h3 := mul_nonneg (mul_nonneg hub hu) (hC12 i)
    linarith
  have hstation : ∀ i,
      p08MatVec (p08Lemma43Propagation constants)
          (p08Lemma43StationaryVector constants) i +
        p08Lemma43RecurrenceForcing constants i =
      p08Lemma43StationaryVector constants i := by
    intro i
    simp only [p08Lemma43Propagation, p08Lemma43StationaryVector,
      p08Lemma43RecurrenceForcing]
    conv_rhs =>
      rw [constants.C11_fixed_point, constants.C12_fixed_point]
    simp only [p08MatVec_add, p08MatVec_scale,
      p08MatVec_matAdd, p08MatVec_matScale,
      p08MatVec_matMul, p08MatVec_id]
    dsimp only [p08VecAdd, p08VecScale]
    ring
  intro m
  induction m with
  | zero =>
      intro i
      simp only [p08Lemma43Bound, p08MatPow, p08MatVec_id,
        p08VecAdd]
      exact (hbase i).trans (le_add_of_nonneg_right
        (hstation_nonnegative i))
  | succ m ih =>
      intro i
      have hm : ∀ i,
          p08MatVec (p08Lemma43Propagation constants)
              (p08AbsVec
                (p08ExactResidualAfterCorrection run m)) i ≤
            p08MatVec (p08Lemma43Propagation constants)
              (p08Lemma43Bound constants m) i := by
        apply p08MatVec_mono hprop_nonnegative
        intro j
        exact ih j
      calc
        |p08ExactResidualAfterCorrection run (m + 1) i| ≤
            p08MatVec (p08Lemma43Propagation constants)
                (p08AbsVec
                  (p08ExactResidualAfterCorrection run m)) i +
              p08Lemma43RecurrenceForcing constants i := hrec m i
        _ ≤ p08MatVec (p08Lemma43Propagation constants)
                (p08Lemma43Bound constants m) i +
              p08Lemma43RecurrenceForcing constants i := by
          exact add_le_add (hm i) (le_refl _)
        _ = p08Lemma43Bound constants (m + 1) i := by
          simp only [p08Lemma43Bound, p08MatPow,
            p08MatVec_add, p08MatVec_matMul, p08VecAdd]
          linarith [hstation i]

end HighamBench
