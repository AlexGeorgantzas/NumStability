import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.ComplexBackwardError
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.ComplexArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints

/-!
# Chapter10 Equation30 ComplexPositiveDefinite SourceClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch10ComplexPositiveDefiniteSourceClosure` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- The positive-definite real part in the two-by-two discrepancy witness. -/
def higham10_30_relaxedCounterB : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else 0

/-- A symmetric, but indefinite, imaginary part. -/
def higham10_30_relaxedCounterC : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else 4

/-- Exact lower factor produced by no-pivot elimination on the witness. -/
noncomputable def higham10_30_relaxedCounterL : Fin 2 → Fin 2 → ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 0 then 4 * Complex.I
    else if i = 1 ∧ j = 1 then 1
    else 0

/-- Exact upper factor produced by no-pivot elimination on the witness. -/
noncomputable def higham10_30_relaxedCounterU : Fin 2 → Fin 2 → ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 0 ∧ j = 1 then 4 * Complex.I
    else if i = 1 ∧ j = 1 then 17
    else 0

theorem higham10_30_relaxedCounterB_spd :
    IsSymPosDef 2 higham10_30_relaxedCounterB := by
  constructor
  · intro i j
    simp only [higham10_30_relaxedCounterB]
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hji => h hji.symm
      simp [h, h']
  · intro x hx
    simp only [Fin.sum_univ_two, higham10_30_relaxedCounterB]
    simp only [ite_true, Fin.zero_ne_one, ite_false]
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · simp_all
      nlinarith [mul_self_pos.mpr hi, sq_nonneg (x 1)]
    · simp_all
      nlinarith [sq_nonneg (x 0), mul_self_pos.mpr hi]

theorem higham10_30_relaxedCounterC_symmetric :
    ∀ i j, higham10_30_relaxedCounterC i j = higham10_30_relaxedCounterC j i := by
  intro i j
  simp only [higham10_30_relaxedCounterC]
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [h, h']

theorem higham10_30_relaxedCounter_exact_lu :
    higham9_8_ComplexLUFactSpec 2
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC)
      higham10_30_relaxedCounterL higham10_30_relaxedCounterU := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [higham10_30_relaxedCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [higham10_30_relaxedCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [higham10_30_relaxedCounterU]
  · intro i j
    fin_cases i
    · fin_cases j
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
        ring
    · fin_cases j
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm]
        ring
      · norm_num [Fin.sum_univ_two, higham10_30_relaxedCounterB,
          higham10_30_relaxedCounterC, higham10_30_relaxedCounterL,
          higham10_30_relaxedCounterU,
          higham10_30_complexPositiveDefiniteForm, Complex.I_sq]
        have hI : (4 : ℂ) * Complex.I * (4 * Complex.I) = -16 := by
          calc
            (4 : ℂ) * Complex.I * (4 * Complex.I) =
                16 * (Complex.I * Complex.I) := by ring
            _ = -16 := by rw [Complex.I_mul_I]; norm_num
        rw [hI]
        norm_num

theorem higham10_30_relaxedCounter_input_max_eq_four :
    higham9_13_complexMaxEntryNorm (by decide : 0 < 2)
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC) = 4 := by
  let A := higham10_30_complexPositiveDefiniteForm 2
    higham10_30_relaxedCounterB higham10_30_relaxedCounterC
  apply le_antisymm
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, higham10_30_complexPositiveDefiniteForm,
        higham10_30_relaxedCounterB, higham10_30_relaxedCounterC,
        norm_mul]
  · have h := higham9_13_entry_norm_le_complexMaxEntryNorm
      (by decide : 0 < 2) A (0 : Fin 2) (1 : Fin 2)
    norm_num [A, higham10_30_complexPositiveDefiniteForm,
      higham10_30_relaxedCounterB, higham10_30_relaxedCounterC,
      norm_mul] at h
    exact h

theorem higham10_30_relaxedCounter_upper_max_eq_seventeen :
    higham9_13_complexMaxEntryNorm (by decide : 0 < 2)
      higham10_30_relaxedCounterU = 17 := by
  apply le_antisymm
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham10_30_relaxedCounterU, norm_mul]
  · have h := higham9_13_entry_norm_le_complexMaxEntryNorm
      (by decide : 0 < 2) higham10_30_relaxedCounterU (1 : Fin 2) (1 : Fin 2)
    norm_num [higham10_30_relaxedCounterU] at h
    exact h

/-- With only `B` positive definite and `C` symmetric, the requested
    `rho < 3` assertion is false: the exact no-pivot upper factor has growth
    `17/4`. -/
theorem higham10_30_relaxedCounter_growth_gt_three :
    3 < higham9_13_complexGrowthFactorEntry (by decide : 0 < 2)
      (higham10_30_complexPositiveDefiniteForm 2
        higham10_30_relaxedCounterB higham10_30_relaxedCounterC)
      higham10_30_relaxedCounterU := by
  rw [higham9_13_complexGrowthFactorEntry,
    higham10_30_relaxedCounter_input_max_eq_four,
    higham10_30_relaxedCounter_upper_max_eq_seventeen]
  norm_num

/-- Real quadratic form in the repository's function-shaped matrix style. -/
noncomputable def higham10_30_realQuadForm {n : ℕ}
    (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j

/-- Bilinear complex quadratic form `zᴴ A z`. -/
noncomputable def higham10_30_complexQuadForm {n : ℕ}
    (A : Fin n → Fin n → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (z i) * A i j * z j

/-- The leading principal restriction of a real matrix. -/
noncomputable def higham10_30_leadingRealBlock {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    Fin k → Fin k → ℝ :=
  fun i j => M (Fin.castLE hk i) (Fin.castLE hk j)

/-- Complex analogue of Theorem 9.1's existence direction: nonvanishing
    leading principal minors give an exact unit-lower/upper no-pivot LU
    certificate. -/
theorem higham10_30_complexLU_exists_of_leadingPrincipalBlock_det_ne_zero :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℂ,
      (∀ k : ℕ, ∀ hk : k ≤ n,
        Matrix.det
          (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0) →
      ∃ L U : Fin n → Fin n → ℂ,
        higham9_8_ComplexLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hlead
      refine ⟨A, A, ?_⟩
      exact
        { L_diag := fun i => i.elim0
          L_upper_zero := fun i => i.elim0
          U_lower_zero := fun i => i.elim0
          product_eq := fun i => i.elim0 }
  | succ m ih =>
      intro A hlead
      have h1le : (1 : ℕ) ≤ m + 1 := by omega
      have hpivot : A 0 0 ≠ 0 := by
        have hdet := hlead 1 h1le
        simpa using hdet
      let S : Fin m → Fin m → ℂ :=
        higham9_8_complexFirstSchurComplement A
      have hSlead : ∀ k : ℕ, ∀ hk : k ≤ m,
          Matrix.det
            (fun i j : Fin k => S (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp
        · have hk1 : k + 1 ≤ m + 1 := by omega
          let Ak : Fin (k + 1) → Fin (k + 1) → ℂ :=
            fun i j => A (Fin.castLE hk1 i) (Fin.castLE hk1 j)
          have hpivotAk : Ak 0 0 ≠ 0 := by
            simpa [Ak, Fin.castLE] using hpivot
          have hdetAk :
              Matrix.det (Matrix.of Ak : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ≠ 0 := by
            simpa [Ak] using hlead (k + 1) hk1
          have hdetSchur :=
            higham9_8_complexFirstSchurComplement_det_ne_zero
              Ak hpivotAk hdetAk
          simpa [S, Ak, higham9_8_complexFirstSchurComplement,
            Fin.castLE] using hdetSchur
      obtain ⟨L₁, U₁, hLU₁⟩ := ih S hSlead
      exact
        ⟨higham9_8_complexLUFirstStepL A L₁,
          higham9_8_complexLUFirstStepU A U₁,
          higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit
            hpivot hLU₁⟩

/-- The rounded upper-entry fold in complex Doolittle elimination.  Each
    complex product and subtraction is implemented by the real-component
    operations from Chapter 3. -/
noncomputable def higham10_30_flComplexDoolittleUEntry (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (k j : Fin n) : ℂ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fl_complexSub fp acc
        (fl_complexMul fp (L k ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ j)))
    (A k j)

/-- The rounded lower-entry numerator in complex Doolittle elimination. -/
noncomputable def higham10_30_flComplexDoolittleLNumerator (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (i k : Fin n) : ℂ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fl_complexSub fp acc
        (fl_complexMul fp (L i ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ k)))
    (A i k)

/-- The rounded lower entry, using the ordinary real-component complex
    division formula (3.14c). -/
noncomputable def higham10_30_flComplexDoolittleLEntry (fp : FPModel) (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (i k : Fin n) : ℂ :=
  fl_complexDiv fp
    (higham10_30_flComplexDoolittleLNumerator fp n A L U i k) (U k k)

/-- One upper-row write of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleStageUpdateU (fp : FPModel) {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) (k : Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    if _hi : i = k then
      if _hj : j.val < k.val then 0
      else higham10_30_flComplexDoolittleUEntry fp n A L U k j
    else U i j

/-- One lower-column write of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleStageUpdateL (fp : FPModel) {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) (k : Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    if _hj : j = k then
      if _hi : i.val < k.val then 0
      else if _hik : k.val < i.val then
        higham10_30_flComplexDoolittleLEntry fp n A L U i k
      else 1
    else L i j

/-- State of the literal square complex Doolittle loop. -/
abbrev higham10_30_ComplexDoolittleState (n : ℕ) :=
  (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)

/-- One literal complex Doolittle stage: write the active upper row first,
    then the active lower column using the newly written pivot. -/
noncomputable def higham10_30_complexDoolittleStageStep (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) (k : Fin n)
    (state : higham10_30_ComplexDoolittleState n) :
    higham10_30_ComplexDoolittleState n :=
  let U₁ := higham10_30_complexDoolittleStageUpdateU fp A state.1 state.2 k
  (higham10_30_complexDoolittleStageUpdateL fp A state.1 U₁ k, U₁)

/-- The first `T` stages of the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleLoopState (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    ∀ T : ℕ, T ≤ n → higham10_30_ComplexDoolittleState n
  | 0, _ => (fun _ _ => 0, fun _ _ => 0)
  | T + 1, hT =>
      let prev := higham10_30_complexDoolittleLoopState fp A T
        (Nat.le_of_succ_le hT)
      higham10_30_complexDoolittleStageStep fp A
        ⟨T, Nat.lt_of_succ_le hT⟩ prev

/-- Computed lower factor returned by the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleL (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (higham10_30_complexDoolittleLoopState fp A n (Nat.le_refl n)).1

/-- Computed upper factor returned by the literal complex Doolittle loop. -/
noncomputable def higham10_30_complexDoolittleU (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (higham10_30_complexDoolittleLoopState fp A n (Nat.le_refl n)).2

/-- The operation-level relative-error certificate used by the complex GE
    backward-error argument.  It is the complex analogue of the usual
    accumulated product representation: each reconstructed entry of `A` has
    one relative perturbation per inner-product term. -/
def higham10_30_ComplexGERelErrorCertificate (n : ℕ)
    (A Lhat Uhat : Fin n → Fin n → ℂ) (γ : ℝ) : Prop :=
  ∀ i j : Fin n, ∃ η : Fin n → ℂ,
    (∀ k, ‖η k‖ ≤ γ) ∧
      A i j = ∑ k : Fin n, Lhat i k * Uhat k j * (1 + η k)

/-- A complex GE relative-error certificate yields the standard componentwise
    backward error `A + ΔA = Lhat Uhat`, with
    `|ΔA| ≤ γ |Lhat||Uhat|`. -/
theorem higham10_30_complexGE_backward_error
    {n : ℕ} {A Lhat Uhat : Fin n → Fin n → ℂ} {γ : ℝ}
    (_hγ : 0 ≤ γ)
    (hcert : higham10_30_ComplexGERelErrorCertificate n A Lhat Uhat γ) :
    ∃ ΔA : Fin n → Fin n → ℂ,
      (∀ i j,
        ‖ΔA i j‖ ≤ γ * ∑ k : Fin n, ‖Lhat i k‖ * ‖Uhat k j‖) ∧
      (∀ i j,
        ∑ k : Fin n, Lhat i k * Uhat k j = A i j + ΔA i j) := by
  let ΔA : Fin n → Fin n → ℂ :=
    fun i j => (∑ k : Fin n, Lhat i k * Uhat k j) - A i j
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    obtain ⟨η, hη, hA⟩ := hcert i j
    have hΔ :
        ΔA i j = -∑ k : Fin n, Lhat i k * Uhat k j * η k := by
      simp only [ΔA]
      rw [hA]
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
      ring
    rw [hΔ, norm_neg]
    calc
      ‖∑ k : Fin n, Lhat i k * Uhat k j * η k‖ ≤
          ∑ k : Fin n, ‖Lhat i k * Uhat k j * η k‖ :=
        norm_sum_le _ _
      _ = ∑ k : Fin n, (‖Lhat i k‖ * ‖Uhat k j‖) * ‖η k‖ := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [norm_mul]
      _ ≤ ∑ k : Fin n, (‖Lhat i k‖ * ‖Uhat k j‖) * γ := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hη k)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = γ * ∑ k : Fin n, ‖Lhat i k‖ * ‖Uhat k j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  · intro i j
    simp [ΔA]

end NumStability
