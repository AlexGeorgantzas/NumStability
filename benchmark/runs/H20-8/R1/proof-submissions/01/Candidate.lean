import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace HighamBenchCandidate

open NumStability

/-- The matrix-only value at the zero approximate solution, including `b = 0`. -/
noncomputable def zeroSolutionMatrixOnlyValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  if b = 0 then 0 else vecNorm2 (rectLSRhs A b) / vecNorm2 b

private theorem zero_minimizer_iff_rhs_zero {m n : ℕ}
    (M : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    IsLeastSquaresMinimizer M b (0 : Fin n → ℝ) ↔
      rectLSRhs M b = 0 := by
  constructor
  · intro h
    have hne := h.rectLSNormalEquations
    funext j
    have hj := hne j
    simpa [RectLSNormalEquations, matMulVec] using hj.symm
  · intro h
    apply RectLSNormalEquations.isLeastSquaresMinimizer
    intro j
    rw [h]
    simp [matMulVec]

private theorem matrix_only_zero_lower_bound {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hfeas : LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
      E (0 : Fin m → ℝ)) :
    vecNorm2 (rectLSRhs A b) ≤ frobNormRect E * vecNorm2 b := by
  have hzero : rectLSRhs (fun i j => A i j + E i j) b = 0 :=
    (zero_minimizer_iff_rhs_zero _ _).mp (by
      simpa [LSNormwiseBackwardErrorFeasible] using hfeas)
  have hneg : rectLSRhs A b = fun j => -rectLSRhs E b j := by
    funext j
    have hj := congrFun hzero j
    simp only [rectLSRhs, Pi.zero_apply, add_mul,
      Finset.sum_add_distrib] at hj ⊢
    linarith
  have hnorm :
      vecNorm2 (rectLSRhs A b) =
        vecNorm2 (rectMatMulVec (finiteTranspose E) b) := by
    rw [hneg]
    simpa [rectLSRhs, rectMatMulVec, finiteTranspose] using
      (vecNorm2_neg (rectLSRhs E b))
  rw [hnorm]
  exact vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul E b

/-- Higham, Problem 20.8: `y = 0`, `θ = ∞`, hence `Δb = 0`.
The witness and universal bound state that the value is an attained minimum. -/
theorem target {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b (0 : Fin n → ℝ) =
        zeroSolutionMatrixOnlyValue A b ∧
      ∃ DeltaA : Fin m → Fin n → ℝ,
        LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
          DeltaA (0 : Fin m → ℝ) ∧
        frobNormRect DeltaA = zeroSolutionMatrixOnlyValue A b ∧
        ∀ E : Fin m → Fin n → ℝ,
          LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
            E (0 : Fin m → ℝ) →
          frobNormRect DeltaA ≤ frobNormRect E := by
  by_cases hb : b = 0
  · subst b
    have hmin : IsLeastSquaresMinimizer A (0 : Fin m → ℝ)
        (0 : Fin n → ℝ) :=
      (zero_minimizer_iff_rhs_zero A 0).2 (by
        funext j
        simp [rectLSRhs])
    have hfeas : LSNormwiseBackwardErrorFeasible A (0 : Fin m → ℝ)
        (0 : Fin n → ℝ) (0 : Fin m → Fin n → ℝ)
        (0 : Fin m → ℝ) := by
      simpa [LSNormwiseBackwardErrorFeasible] using hmin
    have hval : zeroSolutionMatrixOnlyValue A (0 : Fin m → ℝ) = 0 := by
      simp [zeroSolutionMatrixOnlyValue]
    constructor
    · simpa [hval] using
        lsNormwiseBackwardErrorMatrixOnlyEtaF_eq_zero_of_isLeastSquaresMinimizer
          A (0 : Fin m → ℝ) (0 : Fin n → ℝ) hmin
    · refine ⟨0, hfeas, ?_, ?_⟩
      · simp [hval, frobNormRect, frobNormSqRect]
      · intro E _
        simpa [frobNormRect, frobNormSqRect] using
          (frobNormRect_nonneg E)
  · let g : Fin n → ℝ := rectLSRhs A b
    let D : ℝ := vecNorm2Sq b
    have hbne : vecNorm2 b ≠ 0 := by
      intro h
      apply hb
      funext i
      exact (vecNorm2_eq_zero_iff b).mp h i
    have hbpos : 0 < vecNorm2 b :=
      lt_of_le_of_ne (vecNorm2_nonneg b) (Ne.symm hbne)
    have hDpos : 0 < D := by
      change 0 < vecNorm2Sq b
      rw [← vecNorm2_sq]
      positivity
    have hDne : D ≠ 0 := ne_of_gt hDpos
    let d : Fin n → ℝ := fun j => (-1 / D) * g j
    let DeltaA : Fin m → Fin n → ℝ := fun i j => b i * d j
    have hDeltaRhs : rectLSRhs DeltaA b = fun j => -g j := by
      funext j
      change (∑ i : Fin m, (b i * d j) * b i) = -g j
      calc
        (∑ i : Fin m, (b i * d j) * b i) =
            d j * (∑ i : Fin m, b i ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = d j * D := rfl
        _ = -g j := by
          dsimp [d]
          field_simp [hDne]
    have hpertRhs : rectLSRhs (fun i j => A i j + DeltaA i j) b = 0 := by
      funext j
      have hj := congrFun hDeltaRhs j
      change (∑ i : Fin m, DeltaA i j * b i) = -g j at hj
      change (∑ i : Fin m, (A i j + DeltaA i j) * b i) = 0
      simp only [add_mul, Finset.sum_add_distrib]
      rw [hj]
      change g j + -g j = 0
      ring
    have hfeas : LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
        DeltaA (0 : Fin m → ℝ) := by
      change IsLeastSquaresMinimizer (fun i j => A i j + DeltaA i j)
        (fun i => b i + (0 : Fin m → ℝ) i) (0 : Fin n → ℝ)
      simpa using (zero_minimizer_iff_rhs_zero
        (fun i j => A i j + DeltaA i j) b).2 hpertRhs
    have hnorm : frobNormRect DeltaA = vecNorm2 g / vecNorm2 b := by
      calc
        frobNormRect DeltaA = vecNorm2 b * vecNorm2 d := by
          exact frobNormRect_outerProduct b d
        _ = vecNorm2 b * (|(-1 / D : ℝ)| * vecNorm2 g) := by
          simp only [d, vecNorm2_smul]
        _ = vecNorm2 g / vecNorm2 b := by
          rw [abs_div, abs_neg, abs_one, abs_of_pos hDpos]
          have hD : D = vecNorm2 b ^ 2 := (vecNorm2_sq b).symm
          rw [hD]
          field_simp [hbne]
    have hval : zeroSolutionMatrixOnlyValue A b =
        vecNorm2 g / vecNorm2 b := by
      simp [zeroSolutionMatrixOnlyValue, hb, g]
    have hminE : ∀ E : Fin m → Fin n → ℝ,
        LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
          E (0 : Fin m → ℝ) →
        frobNormRect DeltaA ≤ frobNormRect E := by
      intro E hE
      have hbound := matrix_only_zero_lower_bound A E b hE
      change vecNorm2 g ≤ frobNormRect E * vecNorm2 b at hbound
      rw [hnorm]
      exact (div_le_iff₀ hbpos).2 (by simpa [mul_comm] using hbound)
    constructor
    · apply le_antisymm
      · calc
          lsNormwiseBackwardErrorMatrixOnlyEtaF A b (0 : Fin n → ℝ)
              ≤ frobNormRect DeltaA :=
                lsNormwiseBackwardErrorMatrixOnlyEtaF_le_frobNorm_of_feasible
                  A b (0 : Fin n → ℝ) DeltaA hfeas
          _ = zeroSolutionMatrixOnlyValue A b := hnorm.trans hval.symm
      · change zeroSolutionMatrixOnlyValue A b ≤
          sInf (lsNormwiseBackwardErrorMatrixOnlyValuesF
            A b (0 : Fin n → ℝ))
        apply le_csInf
          (lsNormwiseBackwardErrorMatrixOnlyValuesF.nonempty
            A b (0 : Fin n → ℝ))
        intro eta heta
        rcases heta with ⟨E, hE, rfl⟩
        calc
          zeroSolutionMatrixOnlyValue A b = frobNormRect DeltaA :=
            (hnorm.trans hval.symm).symm
          _ ≤ frobNormRect E := hminE E hE
    · exact ⟨DeltaA, hfeas, hnorm.trans hval.symm, hminE⟩

end HighamBenchCandidate
