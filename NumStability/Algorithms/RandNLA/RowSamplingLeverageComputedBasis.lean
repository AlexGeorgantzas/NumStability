-- Algorithms/RandNLA/RowSamplingLeverageComputedBasis.lean
--
-- Computed-basis floating-point transfers for Algorithm 2 leverage sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Algorithms.RandNLA.RowSamplingLeverageMGF
import NumStability.Algorithms.RandNLA.Preconditioning

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Algorithm 2 leverage sampling with a computed/stored basis table

The leverage law remains exact by project convention.  This file charges the
non-probability matrix table that is actually used in the sampled sketch:
an exact orthonormal analysis basis `U` may be represented downstream by a
computed table `Uhat : ComputedMatrix fp U`.
-/

/-- A deterministic columnwise upper bound for absolute entries of the exact
leverage-sampled sketch.  Only rows with positive exact leverage probability
are included; zero-probability rows have zero mass under the exact law. -/
noncomputable def leverageExactBasisSampleColumnAbsBudget
    {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin m,
    if 0 < rowSqNormProb U i then
      |rowSampleIncrement s U i j|
    else
      0

/-- A deterministic columnwise upper bound for the contribution of the stored
basis-table error to each sampled sketch entry. -/
noncomputable def leverageComputedBasisSampleColumnEntryBudget
    (fp : FPModel) {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U) (j : Fin n) : ℝ :=
  ∑ i : Fin m,
    if 0 < rowSqNormProb U i then
      Uhat.abs_error i j / |rowSampleScaleDen s U i|
    else
      0

/-- Deterministic columnwise sampled-sketch error budget when Algorithm 2 uses
a computed/stored basis table and computed row-scale denominators. -/
noncomputable def leverageComputedBasisSampleColumnErrorBudget
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) (j : Fin n) : ℝ :=
  let rho := rowScaleComputedDenEffectiveRelError fp (rowSqNormProb U) dhat
  rho * leverageExactBasisSampleColumnAbsBudget s U j +
    (1 + rho) * leverageComputedBasisSampleColumnEntryBudget fp s U Uhat j

/-- Deterministic Gram perturbation budget for an already-computed row sketch
from columnwise exact-entry and error budgets. -/
noncomputable def rowSketchGramFullAbsFpColumnBudget
    (fp : FPModel) {steps n : ℕ}
    (C E : Fin n → ℝ) : ℝ :=
  frobNorm
      (fun j k : Fin n =>
        gamma fp steps *
          ∑ _t : Fin steps, (C j + E j) * (C k + E k)) +
    frobNorm
      (fun j k : Fin n =>
        ∑ _t : Fin steps,
          (E j * C k + C j * E k + E j * E k))

/-- Deterministic Gram perturbation budget for leverage sampling from a
computed/stored basis table and computed row-scale denominators. -/
noncomputable def leverageComputedBasisDenGramBudget
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) : ℝ :=
  rowSketchGramFullAbsFpColumnBudget (steps := s) fp
    (fun j => leverageExactBasisSampleColumnAbsBudget s U j)
    (fun j => leverageComputedBasisSampleColumnErrorBudget fp U Uhat dhat j)

-- ============================================================
-- Actual-input leverage sampling via a right factor A = U C
-- ============================================================

/-- Right-factor congruence `Cᵀ M C` for Algorithm 2 leverage sampling.

This is deliberately local to the Algorithm 2 factored-input endpoint: the
implementation samples rows of the actual matrix `A = U C`, while the exact
leverage law and source concentration theorem are stated on the orthonormal
analysis basis `U`. -/
noncomputable def leverageRightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ a : Fin r, ∑ b : Fin r, C a j * M a b * C b k

/-- A leverage-sampled actual-input Gram formed with probabilities from `U`
and rows from `A = U C`. -/
noncomputable def leverageFactoredInputSampleGram {m r n s : ℕ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) : Fin n → Fin n → ℝ :=
  rowSketchGram
    (rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
      samples)

/-- Columnwise absolute-entry budget for exact leverage sampling of the actual
input `A = U C`. -/
noncomputable def leverageFactoredInputSampleColumnAbsBudget
    {m r n : ℕ} (s : ℕ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin m,
    if 0 < rowSqNormProb U i then
      |rowSampleIncrementWithProb s (preconditionColumns U C)
        (rowSqNormProb U) i j|
    else
      0

/-- Columnwise sampled-sketch error budget for actual-input leverage sampling
when only the leverage denominator and row division are rounded. -/
noncomputable def leverageFactoredInputSampleColumnErrorBudget
    (fp : FPModel) {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) (j : Fin n) : ℝ :=
  rowScaleComputedDenEffectiveRelError fp (rowSqNormProb U) dhat *
    leverageFactoredInputSampleColumnAbsBudget s U C j

/-- Deterministic Gram perturbation budget for the fully computed
actual-input leverage sampled Gram. -/
noncomputable def leverageFactoredInputDenGramBudget
    (fp : FPModel) {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) : ℝ :=
  rowSketchGramFullAbsFpColumnBudget (steps := s) fp
    (fun j => leverageFactoredInputSampleColumnAbsBudget s U C j)
    (fun j => leverageFactoredInputSampleColumnErrorBudget fp U C dhat j)

theorem leverageExactBasisSampleColumnAbsBudget_nonneg
    {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ leverageExactBasisSampleColumnAbsBudget s U j := by
  classical
  unfold leverageExactBasisSampleColumnAbsBudget
  apply Finset.sum_nonneg
  intro i _
  by_cases hprob : 0 < rowSqNormProb U i
  · simp [hprob]
  · simp [hprob]

theorem leverageComputedBasisSampleColumnEntryBudget_nonneg
    (fp : FPModel) {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U) (j : Fin n) :
    0 ≤ leverageComputedBasisSampleColumnEntryBudget fp s U Uhat j := by
  classical
  unfold leverageComputedBasisSampleColumnEntryBudget
  apply Finset.sum_nonneg
  intro i _
  by_cases hprob : 0 < rowSqNormProb U i
  · simp [hprob, div_nonneg (Uhat.abs_error_nonneg i j) (abs_nonneg _)]
  · simp [hprob]

theorem leverageComputedBasisSampleColumnErrorBudget_nonneg
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) (j : Fin n) :
    0 ≤ leverageComputedBasisSampleColumnErrorBudget fp U Uhat dhat j := by
  classical
  unfold leverageComputedBasisSampleColumnErrorBudget
  let rho := rowScaleComputedDenEffectiveRelError fp (rowSqNormProb U) dhat
  have hrho : 0 ≤ rho :=
    rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb U) dhat
  have h1rho : 0 ≤ 1 + rho := by linarith
  exact add_nonneg
    (mul_nonneg hrho (leverageExactBasisSampleColumnAbsBudget_nonneg s U j))
    (mul_nonneg h1rho
      (leverageComputedBasisSampleColumnEntryBudget_nonneg fp s U Uhat j))

theorem leverageFactoredInputSampleColumnAbsBudget_nonneg
    {m r n : ℕ} (s : ℕ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (j : Fin n) :
    0 ≤ leverageFactoredInputSampleColumnAbsBudget s U C j := by
  classical
  unfold leverageFactoredInputSampleColumnAbsBudget
  apply Finset.sum_nonneg
  intro i _
  by_cases hprob : 0 < rowSqNormProb U i
  · simp [hprob]
  · simp [hprob]

theorem leverageFactoredInputSampleColumnErrorBudget_nonneg
    (fp : FPModel) {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U)) (j : Fin n) :
    0 ≤ leverageFactoredInputSampleColumnErrorBudget fp U C dhat j := by
  unfold leverageFactoredInputSampleColumnErrorBudget
  exact mul_nonneg
    (rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb U) dhat)
    (leverageFactoredInputSampleColumnAbsBudget_nonneg s U C j)

/-- Quadratic forms commute with Algorithm 2's local right-factor congruence. -/
theorem finiteQuadraticForm_leverageRightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (x : Fin n → ℝ) :
    finiteQuadraticForm (leverageRightGramCongruence M C) x =
      finiteQuadraticForm M (fun a : Fin r => ∑ j : Fin n, C a j * x j) := by
  classical
  let y : Fin r → ℝ := fun a => ∑ j : Fin n, C a j * x j
  have hmat : ∀ j : Fin n,
      finiteMatVec (leverageRightGramCongruence M C) x j =
        ∑ a : Fin r, C a j * finiteMatVec M y a := by
    intro j
    unfold finiteMatVec leverageRightGramCongruence y
    conv_lhs => arg 2; ext k; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext k; arg 2; ext a; rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring_nf
  calc
    finiteQuadraticForm (leverageRightGramCongruence M C) x
        =
      ∑ j : Fin n, x j * (∑ a : Fin r, C a j * finiteMatVec M y a) := by
        unfold finiteQuadraticForm
        apply Finset.sum_congr rfl
        intro j _
        rw [hmat]
    _ =
      ∑ a : Fin r, (∑ j : Fin n, C a j * x j) * finiteMatVec M y a := by
        conv_lhs => arg 2; ext j; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ =
      finiteQuadraticForm M y := by
        rfl

/-- Loewner order is preserved by Algorithm 2's local right-factor
congruence. -/
theorem finiteLoewnerLe_leverageRightGramCongruence {r n : ℕ}
    {M N : Fin r → Fin r → ℝ} (C : Fin r → Fin n → ℝ)
    (hMN : finiteLoewnerLe M N) :
    finiteLoewnerLe (leverageRightGramCongruence M C)
      (leverageRightGramCongruence N C) := by
  intro x
  rw [finiteQuadraticForm_leverageRightGramCongruence,
    finiteQuadraticForm_leverageRightGramCongruence]
  exact hMN (fun a : Fin r => ∑ j : Fin n, C a j * x j)

theorem leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram
    {r n : ℕ} (C : Fin r → Fin n → ℝ) (ε : ℝ) :
    leverageRightGramCongruence
        (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram C j k := by
  classical
  ext j k
  unfold leverageRightGramCongruence rowGram finiteIdMatrix
  calc
    ∑ a : Fin r, ∑ b : Fin r, C a j * (ε * if a = b then 1 else 0) * C b k
        =
      ∑ a : Fin r, C a j * (ε * 1) * C a k := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          have hneq : a ≠ b := Ne.symm hb
          simp [hneq]
        · intro hnot
          exact (hnot (Finset.mem_univ a)).elim
    _ = ε * ∑ a : Fin r, C a j * C a k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

theorem leverageRightGramCongruence_finiteIdMatrix_eq_rowGram {r n : ℕ}
    (C : Fin r → Fin n → ℝ) :
    leverageRightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C =
      rowGram C := by
  have h := leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1
  simpa using h

theorem leverageRightGramCongruence_neg {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    leverageRightGramCongruence (fun a b => -M a b) C =
      fun j k => -leverageRightGramCongruence M C j k := by
  classical
  ext j k
  unfold leverageRightGramCongruence
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem leverageRightGramCongruence_sub {r n : ℕ}
    (M N : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    leverageRightGramCongruence (fun a b => M a b - N a b) C =
      fun j k => leverageRightGramCongruence M C j k -
        leverageRightGramCongruence N C j k := by
  classical
  ext j k
  unfold leverageRightGramCongruence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Gram matrices commute with deterministic right factors. -/
theorem rowSketchGram_preconditionColumns_eq_leverageRightGramCongruence
    {steps r n : ℕ} (B : Fin steps → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    rowSketchGram (preconditionColumns B C) =
      leverageRightGramCongruence (rowSketchGram B) C := by
  classical
  ext j k
  unfold rowSketchGram preconditionColumns leverageRightGramCongruence
  conv_lhs => arg 2; ext t; rw [Finset.sum_mul]
  conv_lhs => arg 2; ext t; arg 2; ext a; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem rowGram_preconditionColumns_eq_leverageRightGramCongruence
    {m r n : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    rowGram (preconditionColumns U C) =
      leverageRightGramCongruence (rowGram U) C := by
  classical
  ext j k
  unfold rowGram preconditionColumns leverageRightGramCongruence
  conv_lhs => arg 2; ext i; rw [Finset.sum_mul]
  conv_lhs => arg 2; ext i; arg 2; ext a; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Leverage-sampled rows of `A = U C` are right factors of leverage-sampled
rows of `U`. -/
theorem rowSampleSketchWithProb_preconditionColumns_eq
    {m r n s : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) :
    rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
        samples =
      preconditionColumns (rowSampleSketch s U samples) C := by
  classical
  ext t j
  unfold rowSampleSketchWithProb rowSampleSketch rowSampleIncrementWithProb
    rowSampleIncrement preconditionColumns
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp [rowSampleScaleDenWithProb, rowSampleScaleDen, div_eq_mul_inv]
  ring

theorem leverageFactoredInputSampleGram_eq_rightGramCongruence
    {m r n s : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) :
    leverageFactoredInputSampleGram U C samples =
      leverageRightGramCongruence (rowSampleGram s U samples) C := by
  rw [leverageFactoredInputSampleGram,
    rowSampleSketchWithProb_preconditionColumns_eq]
  simpa [rowSampleGram] using
    rowSketchGram_preconditionColumns_eq_leverageRightGramCongruence
      (rowSampleSketch s U samples) C

theorem leverageFactoredInput_error_eq_rightGramCongruence_error
    {m r n s : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) (hU : HasOrthonormalColumns U) :
    (fun j k : Fin n =>
        leverageFactoredInputSampleGram U C samples j k -
          rowGram (preconditionColumns U C) j k) =
      leverageRightGramCongruence
        (fun a b : Fin r =>
          rowSampleGram s U samples a b - finiteIdMatrix a b) C := by
  classical
  have hsample :=
    leverageFactoredInputSampleGram_eq_rightGramCongruence U C samples
  have hgramU : rowGram U = idMatrix r :=
    rowGram_eq_id_of_orthonormal_columns U hU
  have hgram :
      rowGram (preconditionColumns U C) =
        leverageRightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C := by
    rw [rowGram_preconditionColumns_eq_leverageRightGramCongruence, hgramU]
    rfl
  ext j k
  calc
    leverageFactoredInputSampleGram U C samples j k -
        rowGram (preconditionColumns U C) j k
        =
      leverageRightGramCongruence (rowSampleGram s U samples) C j k -
        leverageRightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C j k := by
        rw [hsample, hgram]
    _ =
      leverageRightGramCongruence
        (fun a b : Fin r =>
          rowSampleGram s U samples a b - finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (leverageRightGramCongruence_sub
              (rowSampleGram s U samples)
              (finiteIdMatrix : Fin r → Fin r → ℝ) C) j) k
        simpa using hsub.symm

theorem leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
    {m r n : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (ε : ℝ) :
    leverageRightGramCongruence (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k := by
  have hAgram : rowGram (preconditionColumns U C) = rowGram C := by
    rw [rowGram_preconditionColumns_eq_leverageRightGramCongruence]
    have hgram : rowGram U = idMatrix r :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        leverageRightGramCongruence
            (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  rw [leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram]
  ext j k
  rw [hAgram]

/-- Exact Algorithm 2 equation (7) transferred from the orthonormal analysis
basis to the actual input matrix `A = U C`.

The probability law and leverage probabilities remain the exact law generated
by `U`; the sampled matrix whose Gram appears in the event is the actual input
`preconditionColumns U C`. -/
theorem leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    {m r n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              leverageFactoredInputSampleGram U C samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(leverageFactoredInputSampleGram U C samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hr
  let E : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun a b : Fin r => rowSampleGram s U samples a b - finiteIdMatrix a b)
        (fun a b : Fin r => ε * finiteIdMatrix a b) ∧
      finiteLoewnerLe
        (fun a b : Fin r => -(rowSampleGram s U samples a b - finiteIdMatrix a b))
        (fun a b : Fin r => ε * finiteIdMatrix a b)}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k)}
  have hE : 1 - δ ≤ P.eventProb E := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hr hrVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hsubset : E ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hUpperU, hLowerU⟩
    let ExactU : Fin r → Fin r → ℝ :=
      fun a b => rowSampleGram s U samples a b - finiteIdMatrix a b
    let EpsU : Fin r → Fin r → ℝ :=
      fun a b => ε * finiteIdMatrix a b
    let ExactA : Fin n → Fin n → ℝ :=
      fun j k =>
        leverageFactoredInputSampleGram U C samples j k -
          rowGram (preconditionColumns U C) j k
    let EpsA : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram (preconditionColumns U C) j k
    have hExactA :
        ExactA = leverageRightGramCongruence ExactU C := by
      simpa [ExactA, ExactU] using
        leverageFactoredInput_error_eq_rightGramCongruence_error
          U C samples hU
    have hEpsA :
        leverageRightGramCongruence EpsU C = EpsA := by
      simpa [EpsU, EpsA] using
        leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
          U C hU ε
    have hUpperA :
        finiteLoewnerLe ExactA EpsA := by
      rw [hExactA, ← hEpsA]
      exact finiteLoewnerLe_leverageRightGramCongruence C hUpperU
    have hLowerA :
        finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
      have hcong :
          finiteLoewnerLe
            (leverageRightGramCongruence (fun a b : Fin r => -ExactU a b) C)
            EpsA := by
        rw [← hEpsA]
        exact finiteLoewnerLe_leverageRightGramCongruence C hLowerU
      have hneg :
          (fun j k : Fin n => -ExactA j k) =
            leverageRightGramCongruence (fun a b : Fin r => -ExactU a b) C := by
        rw [hExactA, leverageRightGramCongruence_neg]
      rw [hneg]
      exact hcong
    exact ⟨by simpa [ExactA, EpsA] using hUpperA,
      by simpa [ExactA, EpsA] using hLowerA⟩
  exact hE.trans (FiniteProbability.eventProb_mono P hsubset)

theorem leverageExactBasisSampleColumnAbs_le_budget
    {m n s : ℕ} (U : Fin m → Fin n → ℝ) (samples : RowTrace m s)
    (t : Fin s) (j : Fin n) (hgood : rowTracePositiveProb U samples) :
    |rowSampleSketch s U samples t j| ≤
      leverageExactBasisSampleColumnAbsBudget s U j := by
  classical
  have hprob : 0 < rowSqNormProb U (samples t) := hgood t
  unfold leverageExactBasisSampleColumnAbsBudget
  let f : Fin m → ℝ := fun i =>
    if 0 < rowSqNormProb U i then |rowSampleIncrement s U i j| else 0
  have hf_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ f i := by
    intro i _
    by_cases hi : 0 < rowSqNormProb U i
    · simp [f, hi]
    · simp [f, hi]
  have hsingle := Finset.single_le_sum hf_nonneg (Finset.mem_univ (samples t))
  simpa [f, hprob, rowSampleSketch] using hsingle

theorem leverageFactoredInputSampleColumnAbs_le_budget
    {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (samples : RowTrace m s)
    (t : Fin s) (j : Fin n) (hgood : rowTracePositiveProb U samples) :
    |rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
        samples t j| ≤
      leverageFactoredInputSampleColumnAbsBudget s U C j := by
  classical
  have hprob : 0 < rowSqNormProb U (samples t) := hgood t
  unfold leverageFactoredInputSampleColumnAbsBudget
  let f : Fin m → ℝ := fun i =>
    if 0 < rowSqNormProb U i then
      |rowSampleIncrementWithProb s (preconditionColumns U C)
        (rowSqNormProb U) i j|
    else
      0
  have hf_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ f i := by
    intro i _
    by_cases hi : 0 < rowSqNormProb U i
    · simp [f, hi]
    · simp [f, hi]
  have hsingle := Finset.single_le_sum hf_nonneg (Finset.mem_univ (samples t))
  simpa [f, hprob, rowSampleSketchWithProb] using hsingle

theorem fl_rowSampleSketchWithComputedDen_factoredInput_abs_error_bound
    (fp : FPModel) {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (samples : RowTrace m s) (t : Fin s) (j : Fin n)
    (hs : 0 < (s : ℝ)) (hgood : rowTracePositiveProb U samples) :
    |fl_rowSampleSketchWithComputedDen fp (preconditionColumns U C) dhat.den
        samples t j -
      rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
        samples t j| ≤
      leverageFactoredInputSampleColumnErrorBudget fp U C dhat j := by
  classical
  let p : Fin m → ℝ := rowSqNormProb U
  let rho : ℝ := rowScaleComputedDenEffectiveRelError fp p dhat
  let B : ℝ :=
    rowSampleSketchWithProb s (preconditionColumns U C) p samples t j
  have hprob : 0 < p (samples t) := hgood t
  have hrho_nonneg : 0 ≤ rho :=
    rowScaleComputedDenEffectiveRelError_nonneg fp p dhat
  have hround :
      |fl_rowSampleSketchWithComputedDen fp (preconditionColumns U C) dhat.den
          samples t j -
        rowSampleSketchWithProb s (preconditionColumns U C) p samples t j| ≤
        |rowSampleSketchWithProb s (preconditionColumns U C) p samples t j| *
          rho := by
    simpa [p, rho] using
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp (preconditionColumns U C) p dhat samples t j hs hprob
  have hB :=
    leverageFactoredInputSampleColumnAbs_le_budget U C samples t j hgood
  calc
    |fl_rowSampleSketchWithComputedDen fp (preconditionColumns U C) dhat.den
        samples t j -
      rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
        samples t j|
        ≤ |B| * rho := by
          simpa [B, p] using hround
    _ ≤
        leverageFactoredInputSampleColumnAbsBudget s U C j * rho := by
          exact mul_le_mul_of_nonneg_right (by simpa [B, p] using hB) hrho_nonneg
    _ =
        leverageFactoredInputSampleColumnErrorBudget fp U C dhat j := by
          simp [leverageFactoredInputSampleColumnErrorBudget, p, rho, mul_comm]

theorem leverageComputedBasisSampleEntryError_le_budget
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U) (samples : RowTrace m s)
    (t : Fin s) (j : Fin n) (hs : 0 < (s : ℝ))
    (hgood : rowTracePositiveProb U samples) :
    Uhat.abs_error (samples t) j /
        |rowSampleScaleDen s U (samples t)| ≤
      leverageComputedBasisSampleColumnEntryBudget fp s U Uhat j := by
  classical
  have hprob : 0 < rowSqNormProb U (samples t) := hgood t
  have hden : rowSampleScaleDen s U (samples t) ≠ 0 :=
    rowSampleScaleDen_ne_zero s U (samples t) hs hprob
  unfold leverageComputedBasisSampleColumnEntryBudget
  let f : Fin m → ℝ := fun i =>
    if 0 < rowSqNormProb U i then
      Uhat.abs_error i j / |rowSampleScaleDen s U i|
    else
      0
  have hf_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ f i := by
    intro i _
    by_cases hi : 0 < rowSqNormProb U i
    · simp [f, hi, div_nonneg (Uhat.abs_error_nonneg i j) (abs_nonneg _)]
    · simp [f, hi]
  have hsingle := Finset.single_le_sum hf_nonneg (Finset.mem_univ (samples t))
  simpa [f, hprob, hden] using hsingle

/-- Entrywise sampled-sketch error from using a computed/stored basis table and
computed leverage denominators. -/
theorem fl_rowSampleSketchWithComputedBasisDen_abs_error_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (samples : RowTrace m s) (t : Fin s) (j : Fin n)
    (hs : 0 < (s : ℝ)) (hgood : rowTracePositiveProb U samples) :
    |fl_rowSampleSketchWithComputedDen fp Uhat.matrix dhat.den samples t j -
        rowSampleSketch s U samples t j| ≤
      leverageComputedBasisSampleColumnErrorBudget fp U Uhat dhat j := by
  classical
  let p : Fin m → ℝ := rowSqNormProb U
  let rho : ℝ := rowScaleComputedDenEffectiveRelError fp p dhat
  let B : ℝ := rowSampleSketch s U samples t j
  let Braw : ℝ :=
    rowSampleSketchWithProb s Uhat.matrix p samples t j
  let Bfl : ℝ :=
    fl_rowSampleSketchWithComputedDen fp Uhat.matrix dhat.den samples t j
  let e : ℝ :=
    Uhat.abs_error (samples t) j /
      |rowSampleScaleDen s U (samples t)|
  have hprob : 0 < p (samples t) := hgood t
  have hrho_nonneg : 0 ≤ rho :=
    rowScaleComputedDenEffectiveRelError_nonneg fp p dhat
  have hden : rowSampleScaleDen s U (samples t) ≠ 0 :=
    rowSampleScaleDen_ne_zero s U (samples t) hs (by simpa [p] using hprob)
  have hround :
      |Bfl - Braw| ≤ |Braw| * rho := by
    simpa [Bfl, Braw, p, rho] using
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp Uhat.matrix p dhat samples t j hs hprob
  have hbasis :
      |Braw - B| ≤ e := by
    have hentry := Uhat.entry_abs_error_bound (samples t) j
    have hdiv_nonneg : 0 ≤ |rowSampleScaleDen s U (samples t)| :=
      abs_nonneg _
    unfold Braw B rowSampleSketchWithProb rowSampleSketch
      rowSampleIncrementWithProb rowSampleIncrement p
    change
      |Uhat.matrix (samples t) j /
          rowSampleScaleDenWithProb s (rowSqNormProb U) (samples t) -
        U (samples t) j / rowSampleScaleDen s U (samples t)| ≤ e
    have hden_eq :
        rowSampleScaleDenWithProb s (rowSqNormProb U) (samples t) =
          rowSampleScaleDen s U (samples t) := rfl
    rw [hden_eq]
    have hdiff :
        Uhat.matrix (samples t) j / rowSampleScaleDen s U (samples t) -
          U (samples t) j / rowSampleScaleDen s U (samples t) =
        (Uhat.matrix (samples t) j - U (samples t) j) /
          rowSampleScaleDen s U (samples t) := by
      ring
    rw [hdiff, abs_div]
    exact div_le_div_of_nonneg_right hentry hdiv_nonneg
  have hbraw_abs : |Braw| ≤ |B| + e := by
    calc
      |Braw| = |(Braw - B) + B| := by
          congr 1
          ring
      _ ≤ |Braw - B| + |B| := abs_add_le _ _
      _ ≤ e + |B| := add_le_add hbasis le_rfl
      _ = |B| + e := by ring
  have hsplit : Bfl - B = (Bfl - Braw) + (Braw - B) := by ring
  have hlocal :
      |Bfl - B| ≤ |B| * rho + (1 + rho) * e := by
    calc
      |Bfl - B| = |(Bfl - Braw) + (Braw - B)| := by rw [hsplit]
      _ ≤ |Bfl - Braw| + |Braw - B| := abs_add_le _ _
      _ ≤ |Braw| * rho + e := by
          exact add_le_add hround hbasis
      _ ≤ (|B| + e) * rho + e := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hbraw_abs hrho_nonneg) le_rfl
      _ = |B| * rho + (1 + rho) * e := by ring
  have hBbudget :=
    leverageExactBasisSampleColumnAbs_le_budget U samples t j hgood
  have hebudget :=
    leverageComputedBasisSampleEntryError_le_budget
      fp U Uhat samples t j hs hgood
  have h1rho : 0 ≤ 1 + rho := by linarith
  calc
    |Bfl - B| ≤ |B| * rho + (1 + rho) * e := hlocal
    _ ≤
        leverageExactBasisSampleColumnAbsBudget s U j * rho +
          (1 + rho) *
            leverageComputedBasisSampleColumnEntryBudget fp s U Uhat j := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hBbudget hrho_nonneg)
          (mul_le_mul_of_nonneg_left hebudget h1rho)
    _ =
        leverageComputedBasisSampleColumnErrorBudget fp U Uhat dhat j := by
        simp [leverageComputedBasisSampleColumnErrorBudget, p, rho, mul_comm]

/-- Column-budget form of the exact-only Gram perturbation theorem. -/
theorem fl_rowSketchGramDot_abs_perturb_bound_of_column_budget
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ) (C E : Fin n → ℝ)
    (hγ : gammaValid fp steps)
    (hC_nonneg : ∀ j, 0 ≤ C j) (hE_nonneg : ∀ j, 0 ≤ E j)
    (hB : ∀ t j, |B t j| ≤ C j)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ E j) :
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) ≤
      rowSketchGramFullAbsFpColumnBudget (steps := steps) fp C E := by
  classical
  let Emat : Fin steps → Fin n → ℝ := fun _t j => E j
  have hbase :
      frobNorm
        (fun j k =>
          fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) ≤
        rowSketchGramFullAbsFpExactBudget fp B Emat := by
    exact fl_rowSketchGramDot_abs_perturb_bound_exact
      fp B Bhat Emat hγ
      (by intro t j; exact hE_nonneg j)
      (by intro t j; exact hentry t j)
  have hdot :
      rowSketchGramDotRoundoffExactBudget fp B Emat ≤
        frobNorm
          (fun j k : Fin n =>
            gamma fp steps *
              ∑ _t : Fin steps, (C j + E j) * (C k + E k)) := by
    unfold rowSketchGramDotRoundoffExactBudget
    apply frobNorm_le_of_entry_abs_le
    · intro j k
      apply mul_nonneg
      · exact gamma_nonneg fp hγ
      · apply Finset.sum_nonneg
        intro t _
        exact mul_nonneg
          (add_nonneg (hC_nonneg j) (hE_nonneg j))
          (add_nonneg (hC_nonneg k) (hE_nonneg k))
    · intro j k
      have hγ_nonneg : 0 ≤ gamma fp steps := gamma_nonneg fp hγ
      have hsum_nonneg :
          0 ≤ ∑ t : Fin steps, (|B t j| + Emat t j) *
            (|B t k| + Emat t k) := by
        apply Finset.sum_nonneg
        intro t _
        exact mul_nonneg
          (add_nonneg (abs_nonneg _) (hE_nonneg j))
          (add_nonneg (abs_nonneg _) (hE_nonneg k))
      calc
        |gamma fp steps *
            ∑ t : Fin steps, (|B t j| + Emat t j) *
              (|B t k| + Emat t k)|
            =
          gamma fp steps *
            ∑ t : Fin steps, (|B t j| + Emat t j) *
              (|B t k| + Emat t k) := by
            simp [abs_of_nonneg (mul_nonneg hγ_nonneg hsum_nonneg)]
        _ ≤ gamma fp steps *
            ∑ _t : Fin steps, (C j + E j) * (C k + E k) := by
            apply mul_le_mul_of_nonneg_left _ hγ_nonneg
            apply Finset.sum_le_sum
            intro t _
            exact mul_le_mul
              (add_le_add (hB t j) le_rfl)
              (add_le_add (hB t k) le_rfl)
              (add_nonneg (abs_nonneg _) (hE_nonneg k))
              (add_nonneg (hC_nonneg j) (hE_nonneg j))
  have hsketch :
      rowSketchGramAbsPerturbExactBudget B Emat ≤
        frobNorm
          (fun j k : Fin n =>
            ∑ _t : Fin steps,
              (E j * C k + C j * E k + E j * E k)) := by
    unfold rowSketchGramAbsPerturbExactBudget
    apply frobNorm_le_of_entry_abs_le
    · intro j k
      apply Finset.sum_nonneg
      intro t _
      exact add_nonneg
        (add_nonneg
          (mul_nonneg (hE_nonneg j) (hC_nonneg k))
          (mul_nonneg (hC_nonneg j) (hE_nonneg k)))
        (mul_nonneg (hE_nonneg j) (hE_nonneg k))
    · intro j k
      have hsum_nonneg :
          0 ≤ ∑ t : Fin steps,
            (Emat t j * |B t k| + |B t j| * Emat t k +
              Emat t j * Emat t k) := by
        apply Finset.sum_nonneg
        intro t _
        exact add_nonneg
          (add_nonneg
            (mul_nonneg (hE_nonneg j) (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (hE_nonneg k)))
          (mul_nonneg (hE_nonneg j) (hE_nonneg k))
      calc
        |∑ t : Fin steps,
            (Emat t j * |B t k| + |B t j| * Emat t k +
              Emat t j * Emat t k)|
            =
          ∑ t : Fin steps,
            (Emat t j * |B t k| + |B t j| * Emat t k +
              Emat t j * Emat t k) := by
            simp [abs_of_nonneg hsum_nonneg]
        _ ≤ ∑ _t : Fin steps,
            (E j * C k + C j * E k + E j * E k) := by
            apply Finset.sum_le_sum
            intro t _
            exact add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left (hB t k) (hE_nonneg j))
                (mul_le_mul_of_nonneg_right (hB t j) (hE_nonneg k)))
              le_rfl
  calc
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k)
      ≤ rowSketchGramFullAbsFpExactBudget fp B Emat := hbase
    _ ≤ rowSketchGramFullAbsFpColumnBudget (steps := steps) fp C E := by
        unfold rowSketchGramFullAbsFpExactBudget
          rowSketchGramFullAbsFpColumnBudget
        exact add_le_add hdot hsketch

/-- Deterministic fully-floating-point Gram perturbation for Algorithm 2
leverage sampling of the actual input `A = U C`.

The exact leverage law is generated by `U`, while the computed sketch and Gram
use the actual input matrix `preconditionColumns U C`. -/
theorem leverage_fl_rowSampleGramDotWithComputedDen_factoredInput_perturb_bound
    (fp : FPModel) {m r n s : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb U samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
            dhat.den samples j k -
          leverageFactoredInputSampleGram U C samples j k) ≤
      leverageFactoredInputDenGramBudget fp U C dhat := by
  classical
  let B : Fin s → Fin n → ℝ :=
    rowSampleSketchWithProb s (preconditionColumns U C) (rowSqNormProb U)
      samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp (preconditionColumns U C) dhat.den
      samples
  let Cbudget : Fin n → ℝ :=
    fun j => leverageFactoredInputSampleColumnAbsBudget s U C j
  let Ebudget : Fin n → ℝ :=
    fun j => leverageFactoredInputSampleColumnErrorBudget fp U C dhat j
  have hC_nonneg : ∀ j, 0 ≤ Cbudget j := by
    intro j
    exact leverageFactoredInputSampleColumnAbsBudget_nonneg s U C j
  have hE_nonneg : ∀ j, 0 ≤ Ebudget j := by
    intro j
    exact leverageFactoredInputSampleColumnErrorBudget_nonneg fp U C dhat j
  have hB : ∀ t j, |B t j| ≤ Cbudget j := by
    intro t j
    exact leverageFactoredInputSampleColumnAbs_le_budget U C samples t j hgood
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ Ebudget j := by
    intro t j
    exact fl_rowSampleSketchWithComputedDen_factoredInput_abs_error_bound
      fp U C dhat samples t j hs hgood
  have h :=
    fl_rowSketchGramDot_abs_perturb_bound_of_column_budget
      fp B Bhat Cbudget Ebudget hγ hC_nonneg hE_nonneg hB hentry
  simpa [B, Bhat, Cbudget, Ebudget, leverageFactoredInputDenGramBudget,
    fl_rowSampleGramDotWithComputedDen, leverageFactoredInputSampleGram] using h

/-- A two-sided Loewner bound with an arbitrary exact right-hand side is stable
under an additive Frobenius perturbation; the right-hand side gains `τ I`.

This local Algorithm 2 adapter is used for factored inputs, where the exact
right-hand side is `ε AᵀA` rather than `ε I`. -/
theorem leverage_finiteLoewnerLe_two_sided_add_general_of_frobNorm_le {n : ℕ}
    (Exact Delta Eps : Fin n → Fin n → ℝ) {τ : ℝ}
    (hExactUpper : finiteLoewnerLe Exact Eps)
    (hExactLower : finiteLoewnerLe (fun j k => -Exact j k) Eps)
    (hpert : frobNorm Delta ≤ τ) :
    finiteLoewnerLe
        (fun j k : Fin n => Exact j k + Delta j k)
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
  classical
  have hDeltaOp : opNorm2Le Delta τ :=
    opNorm2Le_of_frobNorm_le Delta hpert
  have hDeltaUpper :
      finiteLoewnerLe Delta
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
    have hquad :
        |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
  have hDeltaLower :
      finiteLoewnerLe (fun j k : Fin n => -Delta j k)
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have hDeltaNegOp :
        opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
      have hneg : frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
        simpa [frobNorm_neg] using hpert
      exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
        (fun j k : Fin n => -Delta j k) hDeltaNegOp x
    have hquad :
        |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
          τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self
      (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
  have hUpperAdd := finiteLoewnerLe_add hExactUpper hDeltaUpper
  have hLowerAdd := finiteLoewnerLe_add hExactLower hDeltaLower
  have hLower :
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
    have hLower' :
        finiteLoewnerLe
          (fun j k : Fin n => -Exact j k + -Delta j k)
          (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) :=
      hLowerAdd
    convert hLower' using 1
    ext j k
    ring
  exact ⟨hUpperAdd, hLower⟩

/-- Deterministic computed-basis Gram perturbation for Algorithm 2 leverage
sampling. -/
theorem leverage_fl_rowSampleGramDotWithComputedBasisDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (_hU : HasOrthonormalColumns U) (_hn : 0 < n)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb U samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den samples j k -
          rowSampleGram s U samples j k) ≤
      leverageComputedBasisDenGramBudget fp U Uhat dhat := by
  classical
  let B : Fin s → Fin n → ℝ := rowSampleSketch s U samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp Uhat.matrix dhat.den samples
  let C : Fin n → ℝ := fun j => leverageExactBasisSampleColumnAbsBudget s U j
  let E : Fin n → ℝ :=
    fun j => leverageComputedBasisSampleColumnErrorBudget fp U Uhat dhat j
  have hC_nonneg : ∀ j, 0 ≤ C j := by
    intro j
    exact leverageExactBasisSampleColumnAbsBudget_nonneg s U j
  have hE_nonneg : ∀ j, 0 ≤ E j := by
    intro j
    exact leverageComputedBasisSampleColumnErrorBudget_nonneg fp U Uhat dhat j
  have hB : ∀ t j, |B t j| ≤ C j := by
    intro t j
    exact leverageExactBasisSampleColumnAbs_le_budget U samples t j hgood
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ E j := by
    intro t j
    exact fl_rowSampleSketchWithComputedBasisDen_abs_error_bound
      fp U Uhat dhat samples t j hs hgood
  have h :=
    fl_rowSketchGramDot_abs_perturb_bound_of_column_budget
      fp B Bhat C E hγ hC_nonneg hE_nonneg hB hentry
  simpa [B, Bhat, C, E, leverageComputedBasisDenGramBudget,
    fl_rowSampleGramDotWithComputedDen, rowSampleGram] using h

/-- Fully floating-point Algorithm 2 equation (7) transfer with a computed
basis table and computed row-scale denominators. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U Uhat dhat) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U Uhat dhat) *
                finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hn
  let τ : ℝ := leverageComputedBasisDenGramBudget fp U Uhat dhat
  let Eexact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den samples j k -
            rowSampleGram s U samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb Eexact := by
    simpa [P, Eexact] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDotWithComputedBasisDen_perturb_bound
        fp U hU hn hs hγ Uhat dhat samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (Eexact ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Eexact F δ 0 hE hF
  have hsubset : Eexact ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => rowSampleGram s U samples j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den samples j k -
          rowSampleGram s U samples j k
    have htwo :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hExactUpper (by simpa [Exact] using hExactLower)
        (by simpa [F, Delta, τ] using hpert)
    rcases htwo with ⟨hUpper, hLower⟩
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k)) =
        fun j k : Fin n => -(Exact j k + Delta j k) := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpperComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                samples j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hCompEq]
      exact hUpper
    have hLowerComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                samples j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      exact hLower
    exact ⟨hUpperComp, hLowerComp⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, Eexact, F, G, τ] using hG

/-- Fully floating-point Algorithm 2 equation (7) transfer for an actual input
matrix factored as `A = U C`, with an arbitrary already-certified leverage
denominator table.

This is infrastructure for denominator routines: the concrete final theorem
below instantiates `dhat_i = fl_sqrt (fl_mul s p_i)`. -/
theorem leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m r n s : ℕ} {ε δ : ℝ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  dhat.den samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C dhat *
                  finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  dhat.den samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C dhat *
                  finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hr
  let τ : ℝ := leverageFactoredInputDenGramBudget fp U C dhat
  let Eexact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            leverageFactoredInputSampleGram U C samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n =>
          ε * rowGram (preconditionColumns U C) j k +
            τ * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n =>
          ε * rowGram (preconditionColumns U C) j k +
            τ * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb Eexact := by
    simpa [P, Eexact] using
      leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U C hU hr hrVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hr
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDotWithComputedDen_factoredInput_perturb_bound
        fp U C hs hγ dhat samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (Eexact ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Eexact F δ 0 hE hF
  have hsubset : Eexact ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k =>
        leverageFactoredInputSampleGram U C samples j k -
          rowGram (preconditionColumns U C) j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
            dhat.den samples j k -
          leverageFactoredInputSampleGram U C samples j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram (preconditionColumns U C) j k
    have htwo :=
      leverage_finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hExactUpper (by simpa [Exact] using hExactLower)
        (by simpa [F, Delta, τ] using hpert)
    rcases htwo with ⟨hUpper, hLower⟩
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k)) =
        fun j k : Fin n => -(Exact j k + Delta j k) := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpperComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                dhat.den samples j k -
              rowGram (preconditionColumns U C) j k)
          (fun j k : Fin n =>
            ε * rowGram (preconditionColumns U C) j k +
              τ * finiteIdMatrix j k) := by
      rw [hCompEq]
      simpa [Eps] using hUpper
    have hLowerComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                dhat.den samples j k -
              rowGram (preconditionColumns U C) j k))
          (fun j k : Fin n =>
            ε * rowGram (preconditionColumns U C) j k +
              τ * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      simpa [Eps] using hLower
    exact ⟨hUpperComp, hLowerComp⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, Eexact, F, G, τ] using hG

/-- Fully concrete floating-point Algorithm 2 equation (7) for an actual input
matrix factored as `A = U C`.

The implementation samples from the exact leverage law defined by `U`, computes
the actual input sketch using rows of `A = U C`, forms the concrete denominator
`dhat_i = fl_sqrt (fl_mul s p_i)`, rounds the sampled-row divisions, and
computes the sampled Gram with floating-point dot products. -/
theorem leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m r n s : ℕ} {ε δ : ℝ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ).den
                  samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ) *
                  finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ).den
                  samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ) *
                  finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U C hU hr hrVar hs hγ
      (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_mul U_ij 1` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisMulOneAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flMulOne fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flMulOne fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flMulOne fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flMulOne fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flMulOne fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_add U_ij 0` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisAddZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flAddZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flAddZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flAddZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flAddZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flAddZeroRight fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_sub U_ij 0` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisSubZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flSubZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flSubZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flSubZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flSubZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flSubZeroRight fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

end NumStability
