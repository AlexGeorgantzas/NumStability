/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED94 contributors
-/

import NumStability.Algorithms.PriestFiniteFormat
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder
import NumStability.Analysis.HighamChapter7
import NumStability.Algorithms.HighamChapter8FanInClosure
import NumStability.Algorithms.HighamChapter9DoolittleClosure
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.QR.Higham19Thm6ColPivot

/-!
# Higham Chapters 1--9: source-audit closure lemmas

This module contains source-facing endpoints found missing by the fresh audit of
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Chapters
1--9.  It deliberately builds on the chapter modules instead of duplicating
their algorithm definitions.
-/

namespace NumStability

open Filter Asymptotics
open scoped BigOperators
open scoped Topology

/-! ## Chapter 4, Algorithm 4.3: explicit source-operational closure

Higham's sentence following Algorithm 4.3 assumes only ``certain reasonable
assumptions'' and does not enumerate them.  Consequently there is no unique
book-level proposition whose hypotheses can honestly be reconstructed.  The
literal sentence remains `DEFER-MISSING-PRECISE-STATEMENT`.

The results below give a separate, explicit strengthening for the genuine
finite executor.  They expose the arithmetic assumptions recovered from
Priest's thesis and the two non-target loop estimates needed by its
accumulation argument.  In particular, neither `PriestAllStepsExact` nor
`priestDB_defectBudget` is a field of the operational invariant.
-/

/-- The source arithmetic package used by Priest's proof of doubly compensated
summation.  `A2` and faithfulness are included because they are used to
establish the loop-order and ulp invariants; once those invariants have been
made explicit, the local correction-pair proof itself uses `A1` and `S4`. -/
structure PriestSourceArithmeticAssumptions
    (fmt : FloatingPointFormat) : Prop where
  baseTwo : fmt.beta = 2
  precision : 1 < fmt.t
  A1 : PriestSourceA1 fmt
  A2 : PriestSourceA2 fmt
  S4 : PriestSourceS4 fmt
  faithful : PriestSourceFaithful fmt

/-- Primitive source facts for one sum-and-error pair.  These are finite-format
membership, no-exception, and ulp-lattice facts, rather than an assertion that
the pair is exact. -/
structure PriestSourcePairLoopFacts
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop where
  finiteLeft : fmt.finiteSystem a
  finiteRight : fmt.finiteSystem b
  normalSum : fmt.finiteNormalRange (a + b)
  smallFirstUlp : |a| ≤ |b| → priestSourceUlpMultiple fmt a b

/-- The three primitive pair facts maintained at one literal Priest step.
They concern `(c,x)`, `(s,y)`, and `(t,z)`; the rounded combine `(u,υ)` is
intentionally absent. -/
structure PriestSourceStepLoopFacts
    (fmt : FloatingPointFormat) (xk : ℝ) (state : PriestState) : Prop where
  first : PriestSourcePairLoopFacts fmt state.c xk
  second : PriestSourcePairLoopFacts fmt state.s
    (priestFinite_stepTrace fmt xk state).y
  third : PriestSourcePairLoopFacts fmt
    (priestFinite_stepTrace fmt xk state).t
    (priestFinite_stepTrace fmt xk state).z

/-- Priest's source assumptions turn the primitive three-pair loop facts into
the exact local expansion facts.  The combine remains rounded. -/
theorem priestSource_expansionStep_of_stepLoopFacts
    (fmt : FloatingPointFormat) (hsrc : PriestSourceArithmeticAssumptions fmt)
    (xk : ℝ) (state : PriestState)
    (h : PriestSourceStepLoopFacts fmt xk state) :
    PriestFiniteExpansionStep fmt xk state := by
  let T := priestFinite_stepTrace fmt xk state
  have hfirst := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.first.finiteLeft h.first.finiteRight
    h.first.normalSum h.first.smallFirstUlp
  have hsecond := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.second.finiteLeft h.second.finiteRight
    h.second.normalSum h.second.smallFirstUlp
  have hthird := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.third.finiteLeft h.third.finiteRight
    h.third.normalSum h.third.smallFirstUlp
  have haddComm (a b : ℝ) :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.finiteRoundToEvenOp BasicOp.add b a := by
    simp [FloatingPointFormat.finiteRoundToEvenOp,
      BasicOp.exact, add_comm]
  refine ⟨?_, ?_, ?_⟩
  · simpa [T, priestFinite_stepTrace] using hfirst
  · have hsecond' :
        fmt.finiteRoundToEvenOp BasicOp.add T.y state.s +
            fmt.finiteRoundToEvenOp BasicOp.sub T.y
              (fmt.finiteRoundToEvenOp BasicOp.sub
                (fmt.finiteRoundToEvenOp BasicOp.add T.y state.s)
                state.s) =
          state.s + T.y := by
      simpa [T, haddComm state.s T.y] using hsecond
    simpa [T, priestFinite_stepTrace, add_comm] using hsecond'
  · simpa [T, priestFinite_stepTrace] using hthird

/-- Sum of the exact magnitudes presented to the one deliberately rounded
combine in every tail iteration. -/
noncomputable def priestSourceCombineInputMagnitude
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j : Fin n,
    |(priestFinite_stepTrace fmt
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState (kahanFF_model fmt) x j.val
          (Nat.le_of_lt j.isLt))).u +
      (priestFinite_stepTrace fmt
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState (kahanFF_model fmt) x j.val
          (Nat.le_of_lt j.isLt))).upsilon|

/-- Explicit, non-target loop invariants for the finite Priest executor.

* `operations` keeps all ten primitive operations of every step in the region
  where the literal executor agrees with the analytic safe completion;
* `stepPairs` supplies only finite/normal/ulp facts for the three correction
  pairs;
* `retainedCorrection` and `combineInputs` are the two independent magnitude
  estimates used in the source accumulation.  They mention neither the
  per-step defect nor `priestDB_defectBudget`.
-/
structure PriestSourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop where
  operations : PriestFiniteAllOperations fmt x
  stepPairs : ∀ j : Fin n,
    PriestSourceStepLoopFacts fmt
      (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      (priestPrefixState (kahanFF_model fmt) x j.val
        (Nat.le_of_lt j.isLt))
  retainedCorrection :
    |(fl_priestState (kahanFF_model fmt) x).c| ≤
      fmt.unitRoundoff * |∑ i, x i|
  combineInputs :
    priestSourceCombineInputMagnitude fmt x ≤ |∑ i, x i|

/-- Explicit conditional executor closure for Priest's Algorithm 4.3.

The source input assumptions are displayed, but are not claimed to imply the
operational loop invariant: proving that implication is precisely the global
faithful-rounding induction omitted by Higham's phrase ``certain reasonable
assumptions''.  Given the non-target invariant, `A1`/`S4` make the three
correction pairs exact, ordinary rounding bounds the combine defect, and the
two magnitude estimates yield `priestDB_defectBudget`. -/
theorem priestFinite_defectBudget_of_sourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hsrc : PriestSourceArithmeticAssumptions fmt)
    (_hinput : PriestSourceInputAssumptions fmt x)
    (hloop : PriestSourceOperationalLoopInvariants fmt x) :
    priestDB_defectBudget (kahanFF_model fmt) x := by
  have hstep : ∀ j : Fin n,
      |priestDB_stepDefect (kahanFF_model fmt)
          (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          (priestPrefixState (kahanFF_model fmt) x j.val
            (Nat.le_of_lt j.isLt))| ≤
        fmt.unitRoundoff *
          |(priestFinite_stepTrace fmt
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))).u +
            (priestFinite_stepTrace fmt
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))).upsilon| := by
    intro j
    have hpfx := priestFinite_prefixState_eq_priestPrefixState
      fmt x hloop.operations j.val (Nat.le_of_lt j.isLt)
    have hops := hloop.operations j
    rw [hpfx] at hops
    exact priestFinite_stepDefect_abs_le_combine fmt _ _ hops
      (priestSource_expansionStep_of_stepLoopFacts
        fmt hsrc _ _ (hloop.stepPairs j))
  unfold priestDB_defectBudget
  have hsum :
      (∑ j : Fin n,
          |priestDB_stepDefect (kahanFF_model fmt)
            (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            (priestPrefixState (kahanFF_model fmt) x j.val
              (Nat.le_of_lt j.isLt))|) ≤
        fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
    calc
      (∑ j : Fin n,
          |priestDB_stepDefect (kahanFF_model fmt)
            (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            (priestPrefixState (kahanFF_model fmt) x j.val
              (Nat.le_of_lt j.isLt))|) ≤
          ∑ j : Fin n, fmt.unitRoundoff *
            |(priestFinite_stepTrace fmt
                (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                (priestPrefixState (kahanFF_model fmt) x j.val
                  (Nat.le_of_lt j.isLt))).u +
              (priestFinite_stepTrace fmt
                (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                (priestPrefixState (kahanFF_model fmt) x j.val
                  (Nat.le_of_lt j.isLt))).upsilon| := by
            exact Finset.sum_le_sum (fun j _ => hstep j)
      _ = fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
        rw [priestSourceCombineInputMagnitude, Finset.mul_sum]
  calc
    |(fl_priestState (kahanFF_model fmt) x).c| +
          ∑ j : Fin n,
            |priestDB_stepDefect (kahanFF_model fmt)
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))| ≤
        |(fl_priestState (kahanFF_model fmt) x).c| +
          fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
            exact add_le_add_right hsum _
    _ ≤ fmt.unitRoundoff * |∑ i, x i| +
          fmt.unitRoundoff * |∑ i, x i| := by
      exact add_le_add hloop.retainedCorrection
        (mul_le_mul_of_nonneg_left hloop.combineInputs
          fmt.unitRoundoff_nonneg)
    _ = 2 * (kahanFF_model fmt).u * |∑ i, x i| := by
      change fmt.unitRoundoff * |∑ i, x i| +
          fmt.unitRoundoff * |∑ i, x i| =
        2 * fmt.unitRoundoff * |∑ i, x i|
      ring

/-- Returned-value form of the conditional finite-executor theorem. -/
theorem priestFinite_doublyCompensated_accuracy_of_sourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hsrc : PriestSourceArithmeticAssumptions fmt)
    (hinput : PriestSourceInputAssumptions fmt x)
    (hloop : PriestSourceOperationalLoopInvariants fmt x) :
    |(∑ i, x i) - priestFinite_sum fmt x| ≤
      2 * fmt.unitRoundoff * |∑ i, x i| := by
  rw [priestFinite_sum_eq_fl_priestSum fmt x hloop.operations]
  exact priestDB_doublyCompensated_accuracy (kahanFF_model fmt) x
    (priestFinite_defectBudget_of_sourceOperationalLoopInvariants
      fmt x hsrc hinput hloop)

/-! ## Chapter 7, Corollary 7.6: source SPD scaling endpoint -/

/-- Higham, 2nd ed., Corollary 7.6 / equation (7.23), with all source
semantics exposed.  The Cholesky data certify that `A = RᵀR` is symmetric
positive semidefinite and nonsingular, `Rinv * Rinvᵀ` is its genuine inverse,
the printed diagonal pair is reciprocal, and the displayed inverse-side
scaling is a genuine inverse of `D*A*D`.  The final conjunct is the source
factor-`n` near-optimality bound.

Thus this theorem closes the gap in the lower-level estimate, whose formal
inverse-Gram argument did not itself require `Rinv` to invert `R`. -/
theorem higham7_6_spd_source_scaling_bound
    {n : ℕ} (hn : 0 < n)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hRinv : IsInverse n R Rinv) :
    IsSymmetricFiniteMatrix A ∧
      finitePSD A ∧
      IsInverse n A (ch7CholeskyInverseGram Rinv) ∧
      (∀ j : Fin n,
        ch7SymmetricDiagEquilibratingScale2 A j *
            ch7SymmetricDiagEquilibratingInvScale2 A j = 1) ∧
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) ∧
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (n : ℝ) *
          sInf (ch7SymmetricOp2ScaledCondSet A
            (ch7CholeskyInverseGram Rinv)) := by
  have hAeq : A = matMul n (matTranspose R) R := by
    ext i j
    unfold matMul matTranspose
    exact (hGram i j).symm
  have hArect : A = rectMatMul (finiteTranspose R) R := by
    simpa [rectMatMul, finiteTranspose, matMul, matTranspose] using hAeq
  have hsym : IsSymmetricFiniteMatrix A :=
    IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self R hArect
  have hpsd : finitePSD A :=
    finitePSD_of_eq_rectMatMul_transpose_self R hArect
  have hAinv : IsInverse n A (ch7CholeskyInverseGram Rinv) := by
    rw [hAeq]
    exact corollary7_6_cholesky_inverse_gram_isInverse R Rinv hRinv
  have hrecip : ∀ j : Fin n,
      ch7SymmetricDiagEquilibratingScale2 A j *
          ch7SymmetricDiagEquilibratingInvScale2 A j = 1 := by
    intro j
    have hsqrt : Real.sqrt (A j j) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hdiag j))
    simp [ch7SymmetricDiagEquilibratingScale2,
      ch7SymmetricDiagEquilibratingInvScale2, hsqrt]
  have hscaledInv :
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) :=
    corollary7_6_cholesky_scaled_inverse_gram_isInverse
      A R Rinv
      (ch7SymmetricDiagEquilibratingScale2 A)
      (ch7SymmetricDiagEquilibratingInvScale2 A)
      hGram hRinv hrecip
  exact ⟨hsym, hpsd, hAinv, hrecip, hscaledInv,
    corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings
      hn A R Rinv hGram hGramDiag hdiag⟩

/-! ### Property A optimality following Corollary 7.6 -/

/-- Higham's property A in permutation-free sign form.  The signs split the
indices into the two blocks of the source definition: entries inside either
block are diagonal, while cross-block entries are unrestricted.  Equivalently,
after a simultaneous permutation the matrix has a `2 × 2` block form whose
two diagonal blocks are diagonal. -/
def Higham7PropertyA {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∃ s : Fin n → ℝ,
    (∀ i : Fin n, s i ^ 2 = 1) ∧
      ∀ i j : Fin n,
        s i * A i j * s j = if i = j then A i j else -A i j

/-- Property A is invariant under a simultaneous diagonal congruence. -/
lemma Higham7PropertyA.diagCongr
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : Higham7PropertyA A) (d : Fin n → ℝ) :
    Higham7PropertyA (fun i j : Fin n => d i * A i j * d j) := by
  rcases hA with ⟨s, hs, hsign⟩
  refine ⟨s, hs, ?_⟩
  intro i j
  calc
    s i * (d i * A i j * d j) * s j =
        d i * (s i * A i j * s j) * d j := by ring
    _ = d i * (if i = j then A i j else -A i j) * d j := by
      rw [hsign i j]
    _ = if i = j then d i * A i j * d j else -(d i * A i j * d j) := by
      split <;> ring

/-- Spectral condition ratio for an SPD matrix. -/
noncomputable def higham7SPDConditionRatio
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) : ℝ :=
  finiteMaxEigenvalue hn A hSPD.1 / finiteMinEigenvalue hn A hSPD.1

/-- The SPD condition ratio is invariant under equality of the matrix; its
value is independent of the particular proof of positive definiteness. -/
lemma higham7SPDConditionRatio_congr
    {n : ℕ} (hn : 0 < n) {A B : Fin n → Fin n → ℝ}
    (hAB : A = B) (hA : IsSymPosDef n A) (hB : IsSymPosDef n B) :
    higham7SPDConditionRatio hn A hA =
      higham7SPDConditionRatio hn B hB := by
  subst B
  rfl

/-- The property-A sign involution preserves Euclidean norm. -/
lemma higham7_propertyA_sign_normSq
    {n : ℕ} {s x : Fin n → ℝ}
    (hs : ∀ i : Fin n, s i ^ 2 = 1) :
    (∑ i : Fin n, (s i * x i) ^ 2) = ∑ i : Fin n, x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, hs i, one_mul]

/-- For a unit-diagonal property-A matrix, the sign involution complements
every Rayleigh quadratic form about `1`:
`q_A(Sx) = 2‖x‖₂² - q_A(x)`. -/
lemma higham7_propertyA_quadForm_complement
    {n : ℕ} (A : Fin n → Fin n → ℝ) (s x : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, A i i = 1)
    (hsign : ∀ i j : Fin n,
      s i * A i j * s j = if i = j then A i j else -A i j) :
    (∑ i : Fin n, ∑ j : Fin n,
        (s i * x i) * A i j * (s j * x j)) =
      2 * (∑ i : Fin n, x i ^ 2) -
        ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  classical
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        (s i * x i) * A i j * (s j * x j)) =
        ∑ i : Fin n, ∑ j : Fin n,
          x i * (s i * A i j * s j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (2 * (if i = j then x i ^ 2 else 0) -
            x i * A i j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsign i j]
      by_cases hij : i = j
      · subst j
        simp [hdiag i]
        ring
      · simp [hij]
    _ = 2 * (∑ i : Fin n, x i ^ 2) -
          ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
      simp_rw [Finset.sum_sub_distrib]
      simp [Finset.mul_sum, Finset.sum_mul]

/-- An SPD matrix has a strictly positive finite minimum eigenvalue. -/
lemma higham7_finiteMinEigenvalue_pos_of_spd
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    0 < finiteMinEigenvalue hn A hSPD.1 := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn A hSPD.1
  let x : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSPD.1).eigenvectorBasis a)
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSPD.1 a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSPD.1 a
  rw [hnorm, mul_one] at hq
  have hxsq : ∑ i : Fin n, x i ^ 2 = 1 := by
    simpa [x, finiteVecNorm2Sq] using hnorm
  have hx : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : (∑ i : Fin n, x i ^ 2) = 0 := by simp [h]
    linarith
  have hpos := hSPD.2 x hx
  have hqv :
      (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) =
        finiteMinEigenvalue hn A hSPD.1 := by
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  rwa [hqv] at hpos

/-- The extreme eigenvalues of a unit-diagonal symmetric property-A matrix
are paired about `1`: `λ_min + λ_max = 2`. -/
theorem higham7_propertyA_min_add_max_eq_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix A)
    (hdiag : ∀ i : Fin n, A i i = 1)
    (hA : Higham7PropertyA A) :
    finiteMinEigenvalue hn A hSym + finiteMaxEigenvalue hn A hSym = 2 := by
  rcases hA with ⟨s, hs, hsign⟩
  obtain ⟨amax, hamax⟩ := exists_finiteMaxEigenvalue_eq hn A hSym
  let xmax : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSym).eigenvectorBasis amax)
  have hmaxNorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSym amax
  have hmaxQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSym amax
  rw [hmaxNorm, mul_one] at hmaxQ
  have hmaxNorm' : ∑ i : Fin n, xmax i ^ 2 = 1 := by
    simpa [xmax, finiteVecNorm2Sq] using hmaxNorm
  have hmaxQ' :
      (∑ i : Fin n, ∑ j : Fin n, xmax i * A i j * xmax j) =
        finiteMaxEigenvalue hn A hSym := by
    rw [← hamax, ← hmaxQ, finiteQuadraticForm_eq_sum_sum]
  have hminAtSigned := finiteMinEigenvalue_rayleigh hn A hSym
    (fun i => s i * xmax i)
  have hsignedMaxNorm :
      (∑ i : Fin n, (s i * xmax i) ^ 2) = 1 := by
    rw [higham7_propertyA_sign_normSq hs, hmaxNorm']
  have hsignedMaxQ :
      (∑ i : Fin n, ∑ j : Fin n,
        (s i * xmax i) * A i j * (s j * xmax j)) =
        2 - finiteMaxEigenvalue hn A hSym := by
    rw [higham7_propertyA_quadForm_complement A s xmax hdiag hsign,
      hmaxNorm', hmaxQ']
    ring
  rw [hsignedMaxNorm, mul_one, hsignedMaxQ] at hminAtSigned

  obtain ⟨amin, hamin⟩ := exists_finiteMinEigenvalue_eq hn A hSym
  let xmin : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hSym).eigenvectorBasis amin)
  have hminNorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    A hSym amin
  have hminQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hSym amin
  rw [hminNorm, mul_one] at hminQ
  have hminNorm' : ∑ i : Fin n, xmin i ^ 2 = 1 := by
    simpa [xmin, finiteVecNorm2Sq] using hminNorm
  have hminQ' :
      (∑ i : Fin n, ∑ j : Fin n, xmin i * A i j * xmin j) =
        finiteMinEigenvalue hn A hSym := by
    rw [← hamin, ← hminQ, finiteQuadraticForm_eq_sum_sum]
  have hmaxAtSigned := finiteMaxEigenvalue_rayleigh hn A hSym
    (fun i => s i * xmin i)
  have hsignedMinNorm :
      (∑ i : Fin n, (s i * xmin i) ^ 2) = 1 := by
    rw [higham7_propertyA_sign_normSq hs, hminNorm']
  have hsignedMinQ :
      (∑ i : Fin n, ∑ j : Fin n,
        (s i * xmin i) * A i j * (s j * xmin j)) =
        2 - finiteMinEigenvalue hn A hSym := by
    rw [higham7_propertyA_quadForm_complement A s xmin hdiag hsign,
      hminNorm', hminQ']
    ring
  rw [hsignedMinNorm, mul_one, hsignedMinQ] at hmaxAtSigned
  linarith

/-- Forsythe--Straus optimality quoted after Corollary 7.6: an SPD,
unit-diagonal property-A matrix has no better positive diagonal congruence in
the spectral condition-number ratio.  The proof uses the property-A sign
involution to pair the extreme eigenvalues, then tests an arbitrary congruence
on the sign-paired extremal vectors. -/
theorem higham7_propertyA_unitDiagonal_scaling_isOptimal
    {n : ℕ} (hn : 0 < n) (H : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hA : Higham7PropertyA H)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i) :
    finiteMaxEigenvalue hn H hSPD.1 /
        finiteMinEigenvalue hn H hSPD.1 ≤
      finiteMaxEigenvalue hn
          (fun i j : Fin n => d i * H i j * d j)
          (isSymPosDef_diagCongr n d H hd hSPD).1 /
        finiteMinEigenvalue hn
          (fun i j : Fin n => d i * H i j * d j)
          (isSymPosDef_diagCongr n d H hd hSPD).1 := by
  let M : Fin n → Fin n → ℝ := fun i j => d i * H i j * d j
  have hMSPD : IsSymPosDef n M := isSymPosDef_diagCongr n d H hd hSPD
  change finiteMaxEigenvalue hn H hSPD.1 /
      finiteMinEigenvalue hn H hSPD.1 ≤
    finiteMaxEigenvalue hn M hMSPD.1 /
      finiteMinEigenvalue hn M hMSPD.1
  rcases hA with ⟨s, hs, hsign⟩
  have hpair :
      finiteMinEigenvalue hn H hSPD.1 +
          finiteMaxEigenvalue hn H hSPD.1 = 2 :=
    higham7_propertyA_min_add_max_eq_two hn H hSPD.1 hdiag
      ⟨s, hs, hsign⟩
  have hminHpos := higham7_finiteMinEigenvalue_pos_of_spd hn H hSPD
  have hminMpos := higham7_finiteMinEigenvalue_pos_of_spd hn M hMSPD
  let i0 : Fin n := ⟨0, hn⟩
  have hminlemaxH :
      finiteMinEigenvalue hn H hSPD.1 ≤
        finiteMaxEigenvalue hn H hSPD.1 :=
    (finiteMinEigenvalue_le hn H hSPD.1 i0).trans
      (le_finiteMaxEigenvalue hn H hSPD.1 i0)
  have hminlemaxM :
      finiteMinEigenvalue hn M hMSPD.1 ≤
        finiteMaxEigenvalue hn M hMSPD.1 :=
    (finiteMinEigenvalue_le hn M hMSPD.1 i0).trans
      (le_finiteMaxEigenvalue hn M hMSPD.1 i0)
  have hmaxMnonneg : 0 ≤ finiteMaxEigenvalue hn M hMSPD.1 :=
    (le_of_lt hminMpos).trans hminlemaxM

  obtain ⟨amax, hamax⟩ := exists_finiteMaxEigenvalue_eq hn H hSPD.1
  let x : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H hSPD.1).eigenvectorBasis amax)
  have hxnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    H hSPD.1 amax
  have hxQ :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      H hSPD.1 amax
  rw [hxnorm, mul_one] at hxQ
  have hxnorm' : ∑ i : Fin n, x i ^ 2 = 1 := by
    simpa [x, finiteVecNorm2Sq] using hxnorm
  have hxQ' :
      (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) =
        finiteMaxEigenvalue hn H hSPD.1 := by
    rw [← hamax, ← hxQ, finiteQuadraticForm_eq_sum_sum]
  have hxne : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : (∑ i : Fin n, x i ^ 2) = 0 := by simp [h]
    linarith

  let z : Fin n → ℝ := fun i => x i / d i
  let zs : Fin n → ℝ := fun i => (s i * x i) / d i
  have hzne : ∃ i : Fin n, z i ≠ 0 := by
    rcases hxne with ⟨i, hi⟩
    exact ⟨i, div_ne_zero hi (ne_of_gt (hd i))⟩
  have hzsqpos : 0 < ∑ i : Fin n, z i ^ 2 :=
    sum_sq_pos_of_exists_ne n z hzne
  have hzsNorm : (∑ i : Fin n, zs i ^ 2) = ∑ i : Fin n, z i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [zs, z]
    rw [div_pow, div_pow, mul_pow, hs i, one_mul]
  have hzQuad :
      (∑ i : Fin n, ∑ j : Fin n, z i * M i j * z j) =
        finiteMaxEigenvalue hn H hSPD.1 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, z i * M i j * z j) =
          ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [z, M]
        field_simp [ne_of_gt (hd i), ne_of_gt (hd j)]
      _ = finiteMaxEigenvalue hn H hSPD.1 := hxQ'
  have hzsQuad :
      (∑ i : Fin n, ∑ j : Fin n, zs i * M i j * zs j) =
        finiteMinEigenvalue hn H hSPD.1 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, zs i * M i j * zs j) =
          ∑ i : Fin n, ∑ j : Fin n,
            (s i * x i) * H i j * (s j * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [zs, M]
        field_simp [ne_of_gt (hd i), ne_of_gt (hd j)]
      _ = 2 * (∑ i : Fin n, x i ^ 2) -
          ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j :=
        higham7_propertyA_quadForm_complement H s x hdiag hsign
      _ = finiteMinEigenvalue hn H hSPD.1 := by
        rw [hxnorm', hxQ']
        linarith
  have hmaxBound := finiteMaxEigenvalue_rayleigh hn M hMSPD.1 z
  rw [hzQuad] at hmaxBound
  have hminBound := finiteMinEigenvalue_rayleigh hn M hMSPD.1 zs
  rw [hzsNorm, hzsQuad] at hminBound
  rw [div_le_div_iff₀ hminHpos hminMpos]
  calc
    finiteMaxEigenvalue hn H hSPD.1 * finiteMinEigenvalue hn M hMSPD.1 ≤
        (finiteMaxEigenvalue hn M hMSPD.1 * (∑ i : Fin n, z i ^ 2)) *
          finiteMinEigenvalue hn M hMSPD.1 :=
      mul_le_mul_of_nonneg_right hmaxBound (le_of_lt hminMpos)
    _ = finiteMaxEigenvalue hn M hMSPD.1 *
          (finiteMinEigenvalue hn M hMSPD.1 * (∑ i : Fin n, z i ^ 2)) := by
      ring
    _ ≤ finiteMaxEigenvalue hn M hMSPD.1 *
          finiteMinEigenvalue hn H hSPD.1 :=
      mul_le_mul_of_nonneg_left hminBound hmaxMnonneg

/-- Source-shaped Forsythe--Straus result following Corollary 7.6.  If `A` is
SPD with property A, then the printed scaling
`D* = diag(a_ii^{-1/2})` is optimal among all positive diagonal congruences.
The theorem also returns the genuine SPD certificate and unit diagonal for the
scaled matrix, so the condition ratios are not merely symbolic expressions. -/
theorem higham7_6_propertyA_source_scaling_isOptimal
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) (hA : Higham7PropertyA A)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i) :
    let Dstar : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
    let H : Fin n → Fin n → ℝ := ch7TwoSidedScale Dstar A Dstar
    let M : Fin n → Fin n → ℝ := ch7TwoSidedScale d A d
    ∃ (hHSPD : IsSymPosDef n H) (hMSPD : IsSymPosDef n M),
      Higham7PropertyA H ∧
        (∀ i : Fin n, H i i = 1) ∧
        higham7SPDConditionRatio hn H hHSPD ≤
          higham7SPDConditionRatio hn M hMSPD := by
  dsimp only
  let Dstar : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
  let H : Fin n → Fin n → ℝ := ch7TwoSidedScale Dstar A Dstar
  let M : Fin n → Fin n → ℝ := ch7TwoSidedScale d A d
  have hAdiag : ∀ i : Fin n, 0 < A i i := by
    intro i
    have hi : ∃ k : Fin n, (fun k => if k = i then (1 : ℝ) else 0) k ≠ 0 := by
      exact ⟨i, by simp⟩
    have hpos := hSPD.2 (fun k => if k = i then (1 : ℝ) else 0) hi
    simpa [Finset.sum_ite_eq', Finset.mem_univ] using hpos
  have hDstar : ∀ i : Fin n, 0 < Dstar i := by
    intro i
    dsimp [Dstar, ch7SymmetricDiagEquilibratingScale2]
    exact one_div_pos.mpr (Real.sqrt_pos.2 (hAdiag i))
  have hHSPD : IsSymPosDef n H := by
    dsimp [H, ch7TwoSidedScale]
    exact isSymPosDef_diagCongr n Dstar A hDstar hSPD
  have hMSPD : IsSymPosDef n M := by
    dsimp [M, ch7TwoSidedScale]
    exact isSymPosDef_diagCongr n d A hd hSPD
  have hHA : Higham7PropertyA H := by
    dsimp [H, ch7TwoSidedScale]
    exact hA.diagCongr Dstar
  have hHdiag : ∀ i : Fin n, H i i = 1 := by
    intro i
    dsimp [H, Dstar, ch7TwoSidedScale,
      ch7SymmetricDiagEquilibratingScale2]
    have hsqrt := Real.sqrt_pos.2 (hAdiag i)
    field_simp [ne_of_gt hsqrt]
    nlinarith [Real.sq_sqrt (le_of_lt (hAdiag i))]
  let e : Fin n → ℝ := fun i => d i * Real.sqrt (A i i)
  have he : ∀ i : Fin n, 0 < e i := by
    intro i
    exact mul_pos (hd i) (Real.sqrt_pos.2 (hAdiag i))
  have hscaledEq :
      (fun i j : Fin n => e i * H i j * e j) = M := by
    funext i j
    dsimp [e, H, M, Dstar, ch7TwoSidedScale,
      ch7SymmetricDiagEquilibratingScale2]
    have hi := Real.sqrt_pos.2 (hAdiag i)
    have hj := Real.sqrt_pos.2 (hAdiag j)
    field_simp [ne_of_gt hi, ne_of_gt hj]
  have hopt := higham7_propertyA_unitDiagonal_scaling_isOptimal
    hn H hHSPD hHdiag hHA e he
  change higham7SPDConditionRatio hn H hHSPD ≤
    higham7SPDConditionRatio hn
      (fun i j : Fin n => e i * H i j * e j)
      (isSymPosDef_diagCongr n e H he hHSPD) at hopt
  have hratioEq := higham7SPDConditionRatio_congr hn hscaledEq
    (isSymPosDef_diagCongr n e H he hHSPD) hMSPD
  have hfinal := hopt.trans_eq hratioEq
  simpa [Dstar, H, M] using
    (show ∃ (hHSPD : IsSymPosDef n H) (hMSPD : IsSymPosDef n M),
        Higham7PropertyA H ∧
          (∀ i : Fin n, H i i = 1) ∧
          higham7SPDConditionRatio hn H hHSPD ≤
            higham7SPDConditionRatio hn M hMSPD from
      ⟨hHSPD, hMSPD, hHA, hHdiag, hfinal⟩)

/-! ### Sparse refinements following Corollary 7.6 -/

/-- Complexifying a real column preserves its Euclidean norm, expressed in
the Chapter 6 `p = 2` vector-norm API used by the sparse-row form of (6.23). -/
lemma higham7_complex_column_two_norm_eq_real_column_norm
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (j : Fin n) :
    complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
        (fun i : Fin m => realRectToCMatrix A i j) =
      ch7RectColumnNorm2 A j := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hcomplex := complexVecLpNorm_rpow_eq_sum_rpow
    (p := (2 : ℝ)) (by norm_num) (fun i : Fin m => realRectToCMatrix A i j)
  have hcomplex_sq :
      complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
          (fun i : Fin m => realRectToCMatrix A i j) ^ 2 =
        ∑ i : Fin m, ‖realRectToCMatrix A i j‖ ^ 2 := by
    simpa [Real.rpow_natCast] using hcomplex
  have hreal := vecNorm2_sq (fun i : Fin m => A i j)
  apply (sq_eq_sq₀
    ((complexVecLpNorm_isComplexVectorNorm
      (ENNReal.ofReal (2 : ℝ))).nonneg
        (fun i : Fin m => realRectToCMatrix A i j))
    (ch7RectColumnNorm2_nonneg A j)).mp
  rw [hcomplex_sq]
  rw [show ch7RectColumnNorm2 A j = vecNorm2 (fun i : Fin m => A i j) from rfl,
    hreal]
  simp [realRectToCMatrix, vecNorm2Sq, sq_abs]

/-- A nonzero diagonal right scaling preserves every row support. -/
lemma higham7_complexified_rightScale_rowSupport_eq
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (d : Fin n → ℝ)
    (hd : ∀ j : Fin n, d j ≠ 0) (i : Fin m) :
    complexMatrixRowSupport
        (realRectToCMatrix (ch7RectRightScale A d)) i =
      complexMatrixRowSupport (realRectToCMatrix A) i := by
  classical
  ext j
  simp [complexMatrixRowSupport, realRectToCMatrix, ch7RectRightScale,
    hd j]

/-- Row sparsity is therefore unchanged by the source column-equilibrating
diagonal, whose entries are nonzero when all columns are nonzero. -/
lemma higham7_column_equilibratingScale_preserves_sparseRows
    {m n μ : ℕ} (A : Fin m → Fin n → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    complexMatrixRowsSupportCardLe
      (realRectToCMatrix
        (ch7RectRightScale A (ch7ColumnEquilibratingScale2 A))) μ := by
  intro i
  rw [higham7_complexified_rightScale_rowSupport_eq A
    (ch7ColumnEquilibratingScale2 A)
    (fun j => by
      unfold ch7ColumnEquilibratingScale2
      exact one_div_ne_zero (ne_of_gt (hcol j))) i]
  exact hrows i

/-- Sparse-row strengthening of (7.21): if every row has at most `μ`
nonzeros, column equilibration has operator 2-norm at most `sqrt μ`, replacing
the ambient `sqrt n` factor exactly as stated after Corollary 7.6. -/
theorem higham7_sparseRows_column_equilibrated_op2_le_sqrt
    {m n μ : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    complexMatrixOp2
        (realRectToCMatrix
          (ch7RectRightScale A (ch7ColumnEquilibratingScale2 A))) ≤
      Real.sqrt (μ : ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let B : Fin m → Fin n → ℝ :=
    ch7RectRightScale A (ch7ColumnEquilibratingScale2 A)
  have hrowsB : complexMatrixRowsSupportCardLe (realRectToCMatrix B) μ := by
    dsimp [B]
    exact higham7_column_equilibratingScale_preserves_sparseRows A hcol hrows
  have hsparse :=
    (complexMatrixLpNormOfReal_sparseRows_bounds
      (m := m) (n := n) (μ := μ) hn (p := (2 : ℝ)) (by norm_num)
      hrowsB).2
  have hcolmax :
      complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ)))
          (realRectToCMatrix B) ≤ 1 := by
    apply complexMatrixColumnMaxVectorNorm_le_of_col_le
      (complexVecLpNorm_isComplexVectorNorm
        (ENNReal.ofReal (2 : ℝ))) (by norm_num)
    intro j
    rw [higham7_complex_column_two_norm_eq_real_column_norm B j]
    dsimp [B]
    rw [ch7RectColumnNorm2_rightScale_equilibrating A hcol j]
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2] at hsparse
  calc
    complexMatrixOp2 (realRectToCMatrix B) ≤
        (μ : ℝ) ^ (1 - (2 : ℝ)⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ)))
            (realRectToCMatrix B) := hsparse
    _ ≤ (μ : ℝ) ^ (1 - (2 : ℝ)⁻¹) * 1 :=
      mul_le_mul_of_nonneg_left hcolmax
        (Real.rpow_nonneg (Nat.cast_nonneg μ) _)
    _ = Real.sqrt (μ : ℝ) := by
      norm_num [Real.sqrt_eq_rpow]

/-- Sparse-row version of Theorem 7.5, equation (7.18), at `p = 2`:
the ambient `sqrt n` factor is replaced by the square root of the maximum row
support size. -/
theorem higham7_5_p2_column_equilibration_le_sqrt_sparseRows_right_scaling
    {m n μ : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ)
    (d dInv : Fin n → ℝ)
    (hdiag : ∀ j : Fin n, d j * dInv j = 1) :
    ch7Op2RightScaledCond A Aplus
        (ch7ColumnEquilibratingScale2 A)
        (fun j : Fin n => ch7RectColumnNorm2 A j) ≤
      Real.sqrt (μ : ℝ) * ch7Op2RightScaledCond A Aplus d dInv := by
  unfold ch7Op2RightScaledCond
  let ADc : Fin m → Fin n → ℝ :=
    ch7RectRightScale A (ch7ColumnEquilibratingScale2 A)
  let AplusDcInv : Fin n → Fin m → ℝ :=
    ch7RectLeftScale (fun j : Fin n => ch7RectColumnNorm2 A j) Aplus
  let AD : Fin m → Fin n → ℝ := ch7RectRightScale A d
  let DinvAplus : Fin n → Fin m → ℝ := ch7RectLeftScale dInv Aplus
  have hADc :
      complexMatrixOp2 (realRectToCMatrix ADc) ≤ Real.sqrt (μ : ℝ) := by
    dsimp [ADc]
    exact higham7_sparseRows_column_equilibrated_op2_le_sqrt
      hn A hcol hrows
  have hside :
      complexMatrixOp2 (realRectToCMatrix AplusDcInv) ≤
        complexMatrixOp2 (realRectToCMatrix AD) *
          complexMatrixOp2 (realRectToCMatrix DinvAplus) := by
    dsimp [AplusDcInv, AD, DinvAplus]
    exact eq_7_22_op2_inverseSide_bound A Aplus d dInv hdiag
  have hAplusDcInv_nonneg :
      0 ≤ complexMatrixOp2 (realRectToCMatrix AplusDcInv) :=
    complexMatrixOp2_nonneg _
  calc
    complexMatrixOp2 (realRectToCMatrix ADc) *
        complexMatrixOp2 (realRectToCMatrix AplusDcInv) ≤
      Real.sqrt (μ : ℝ) *
        complexMatrixOp2 (realRectToCMatrix AplusDcInv) :=
      mul_le_mul_of_nonneg_right hADc hAplusDcInv_nonneg
    _ ≤ Real.sqrt (μ : ℝ) *
        (complexMatrixOp2 (realRectToCMatrix AD) *
          complexMatrixOp2 (realRectToCMatrix DinvAplus)) :=
      mul_le_mul_of_nonneg_left hside (Real.sqrt_nonneg _)

/-- Infimum form of the sparse-row Theorem 7.5 refinement. -/
theorem higham7_5_p2_column_equilibration_le_sqrt_sparseRows_sInf
    {m n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hcol : ∀ j : Fin n, 0 < ch7RectColumnNorm2 A j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix A) μ) :
    ch7Op2RightScaledCond A Aplus
        (ch7ColumnEquilibratingScale2 A)
        (fun j : Fin n => ch7RectColumnNorm2 A j) ≤
      Real.sqrt (μ : ℝ) * sInf (ch7Op2RightScaledCondSet A Aplus) := by
  let c : ℝ := ch7Op2RightScaledCond A Aplus
    (ch7ColumnEquilibratingScale2 A)
    (fun j : Fin n => ch7RectColumnNorm2 A j)
  let S : Set ℝ := ch7Op2RightScaledCondSet A Aplus
  let α : ℝ := Real.sqrt (μ : ℝ)
  have hαpos : 0 < α := Real.sqrt_pos.2 (Nat.cast_pos.mpr hμ)
  have hS_nonempty : S.Nonempty := by
    simpa [S] using ch7Op2RightScaledCondSet_nonempty A Aplus
  have hlower : ∀ κ : ℝ, κ ∈ S → c / α ≤ κ := by
    intro κ hκ
    rcases hκ with ⟨d, dInv, hdiag, rfl⟩
    rw [div_le_iff₀ hαpos]
    simpa [c, α, mul_comm] using
      higham7_5_p2_column_equilibration_le_sqrt_sparseRows_right_scaling
        hn A Aplus hcol hrows d dInv hdiag
  have hsInf : c / α ≤ sInf S := le_csInf hS_nonempty hlower
  have hmul := mul_le_mul_of_nonneg_left hsInf (le_of_lt hαpos)
  have hcancel : α * (c / α) = c := by
    field_simp [ne_of_gt hαpos]
  change c ≤ α * sInf S
  exact hcancel ▸ hmul

/-- Sparse-row strengthening of Corollary 7.6.  If every row of the Cholesky
factor `R` has at most `μ` nonzeros, the factor `n` in (7.23) is replaced by
`μ`; this is the printed refinement obtained from sparse equation (6.23). -/
theorem higham7_6_cholesky_scaled_cond_le_sparseRows_sInf
    {n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix R) μ) :
    ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
        (ch7SymmetricDiagEquilibratingScale2 A)
        (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
      (μ : ℝ) *
        sInf (ch7SymmetricOp2ScaledCondSet A
          (ch7CholeskyInverseGram Rinv)) := by
  let d : Fin n → ℝ := ch7SymmetricDiagEquilibratingScale2 A
  let dInv : Fin n → ℝ := ch7SymmetricDiagEquilibratingInvScale2 A
  let c : ℝ := ch7Op2RightScaledCond R Rinv d dInv
  let S : Set ℝ := ch7Op2RightScaledCondSet R Rinv
  let T : Set ℝ :=
    ch7SymmetricOp2ScaledCondSet A (ch7CholeskyInverseGram Rinv)
  have hscale := corollary7_6_cholesky_diag_scale_eq_column_equilibrating
    A R hGramDiag hdiag
  have hinvScale := corollary7_6_cholesky_diag_invScale_eq_column_norm
    A R hGramDiag hdiag
  have hcol := corollary7_6_cholesky_column_norm_pos
    A R hGramDiag hdiag
  have hfactor : c ≤ Real.sqrt (μ : ℝ) * sInf S := by
    dsimp [c, d, dInv, S]
    rw [hscale, hinvScale]
    exact higham7_5_p2_column_equilibration_le_sqrt_sparseRows_sInf
      hn hμ R Rinv hcol hrows
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact ch7Op2RightScaledCond_nonneg R Rinv d dInv
  have hsInf_nonneg : 0 ≤ sInf S := by
    simpa [S] using ch7Op2RightScaledCondSet_sInf_nonneg R Rinv
  have hrhs_nonneg : 0 ≤ Real.sqrt (μ : ℝ) * sInf S :=
    mul_nonneg (Real.sqrt_nonneg _) hsInf_nonneg
  have hsq : c ^ 2 ≤ (Real.sqrt (μ : ℝ) * sInf S) ^ 2 :=
    (sq_le_sq₀ hc_nonneg hrhs_nonneg).mpr hfactor
  have hcond :
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv) d dInv =
        c ^ 2 := by
    dsimp [c]
    exact corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq
      A R Rinv d dInv hGram
  have hsqrt_sq :
      (Real.sqrt (μ : ℝ) * sInf S) ^ 2 =
        (μ : ℝ) * (sInf S) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg μ)]
  have hfactorSq :
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (μ : ℝ) * (sInf S) ^ 2 := by
    rw [show ch7SymmetricDiagEquilibratingScale2 A = d from rfl,
      show ch7SymmetricDiagEquilibratingInvScale2 A = dInv from rfl,
      hcond]
    rw [hsqrt_sq] at hsq
    exact hsq
  have htransfer : (sInf S) ^ 2 ≤ sInf T := by
    simpa [S, T] using
      corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf A R Rinv hGram
  have hmul : (μ : ℝ) * (sInf S) ^ 2 ≤ (μ : ℝ) * sInf T :=
    mul_le_mul_of_nonneg_left htransfer (Nat.cast_nonneg μ)
  exact hfactorSq.trans (by simpa [T] using hmul)

/-- Fully source-facing sparse Corollary 7.6 wrapper: alongside the refined
factor-`μ` estimate, it certifies the SPD semantics, both inverse identities,
and reciprocity of the printed diagonal pair. -/
theorem higham7_6_spd_sparseRows_source_scaling_bound
    {n μ : ℕ} (hn : 0 < n) (hμ : 0 < μ)
    (A R Rinv : Fin n → Fin n → ℝ)
    (hGram : ∀ i j : Fin n, (∑ k : Fin n, R k i * R k j) = A i j)
    (hGramDiag : ∀ j : Fin n, (∑ k : Fin n, R k j * R k j) = A j j)
    (hdiag : ∀ j : Fin n, 0 < A j j)
    (hRinv : IsInverse n R Rinv)
    (hrows : complexMatrixRowsSupportCardLe (realRectToCMatrix R) μ) :
    IsSymmetricFiniteMatrix A ∧
      finitePSD A ∧
      IsInverse n A (ch7CholeskyInverseGram Rinv) ∧
      (∀ j : Fin n,
        ch7SymmetricDiagEquilibratingScale2 A j *
            ch7SymmetricDiagEquilibratingInvScale2 A j = 1) ∧
      IsInverse n
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingScale2 A) A
          (ch7SymmetricDiagEquilibratingScale2 A))
        (ch7TwoSidedScale (ch7SymmetricDiagEquilibratingInvScale2 A)
          (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingInvScale2 A)) ∧
      ch7SymmetricOp2ScaledCond A (ch7CholeskyInverseGram Rinv)
          (ch7SymmetricDiagEquilibratingScale2 A)
          (ch7SymmetricDiagEquilibratingInvScale2 A) ≤
        (μ : ℝ) *
          sInf (ch7SymmetricOp2ScaledCondSet A
            (ch7CholeskyInverseGram Rinv)) := by
  have hbase := higham7_6_spd_source_scaling_bound
    hn A R Rinv hGram hGramDiag hdiag hRinv
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
    hbase.2.2.2.2.1,
    higham7_6_cholesky_scaled_cond_le_sparseRows_sInf
      hn hμ A R Rinv hGram hGramDiag hdiag hrows⟩

/-! ## Chapter 7, equation (7.25): inverse matrix-inf condition -/

/-- The first derivative of inversion at `A`, written using its inverse:
`D(inv)_A[ΔA] = -A⁻¹ ΔA A⁻¹`. -/
noncomputable def higham7_25_inverseLinearizedChange
    (n : ℕ) (Ainv ΔA : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => -matMul n (matMul n Ainv ΔA) Ainv i j

/-- The nonnegative matrix `|A⁻¹| E |A⁻¹|` in the numerator of
Higham's equation (7.25). -/
noncomputable def higham7_25_inverseSensitivity
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (absMatrix n Ainv) E) (absMatrix n Ainv)

/-- Unit-radius componentwise perturbations for equation (7.25). -/
def Higham7_25AdmissiblePerturbation
    {n : ℕ} (E ΔA : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |ΔA i j| ≤ E i j

/-- The sensitivity matrix in (7.25) is componentwise nonnegative. -/
lemma higham7_25_inverseSensitivity_nonneg
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    ∀ i j : Fin n, 0 ≤ higham7_25_inverseSensitivity n Ainv E i j := by
  have hfirst : ∀ i j : Fin n,
      0 ≤ matMul n (absMatrix n Ainv) E i j :=
    ch7_matMul_nonneg n (absMatrix n Ainv) E
      (by intro i j; exact abs_nonneg _) hE
  exact ch7_matMul_nonneg n
    (matMul n (absMatrix n Ainv) E) (absMatrix n Ainv)
    hfirst (by intro i j; exact abs_nonneg _)

/-- Componentwise derivative domination behind the upper bound in (7.25). -/
theorem higham7_25_inverseLinearizedChange_abs_le
    (n : ℕ) (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    ∀ i j : Fin n,
      |higham7_25_inverseLinearizedChange n Ainv ΔA i j| ≤
        higham7_25_inverseSensitivity n Ainv E i j := by
  let M : Fin n → Fin n → ℝ := matMul n Ainv ΔA
  let P : Fin n → Fin n → ℝ := matMul n (absMatrix n Ainv) E
  have hP : ∀ i j : Fin n, 0 ≤ P i j :=
    ch7_matMul_nonneg n (absMatrix n Ainv) E
      (by intro i j; exact abs_nonneg _) hE
  have hM : ∀ i j : Fin n, |M i j| ≤ P i j := by
    intro i j
    have h := ch7_matMul_abs_le_of_scaled_abs_le
      n Ainv ΔA (absMatrix n Ainv) E 1 1
      (by norm_num) (by norm_num)
      (by intro a b; exact abs_nonneg _) hE
      (by intro a b; simp [absMatrix])
      (by intro a b; simpa using hΔ a b) i j
    simpa [M, P] using h
  intro i j
  have h := ch7_matMul_abs_le_of_scaled_abs_le
    n M Ainv P (absMatrix n Ainv) 1 1
    (by norm_num) (by norm_num) hP
    (by intro a b; exact abs_nonneg _)
    (by intro a b; simpa using hM a b)
    (by intro a b; simp [absMatrix]) i j
  simpa [higham7_25_inverseLinearizedChange,
    higham7_25_inverseSensitivity, M, P, abs_neg] using h

/-- Matrix-infinity-norm form of the derivative upper bound in (7.25). -/
theorem higham7_25_inverseLinearizedChange_infNorm_le
    (n : ℕ) (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |higham7_25_inverseLinearizedChange n Ainv ΔA i j| ≤
          ∑ j : Fin n, higham7_25_inverseSensitivity n Ainv E i j :=
        Finset.sum_le_sum (fun j _ =>
          higham7_25_inverseLinearizedChange_abs_le n Ainv E ΔA hE hΔ i j)
      _ = ∑ j : Fin n, |higham7_25_inverseSensitivity n Ainv E i j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg
          (higham7_25_inverseSensitivity_nonneg n Ainv E hE i j)]
      _ ≤ infNorm (higham7_25_inverseSensitivity n Ainv E) :=
        row_sum_le_infNorm (higham7_25_inverseSensitivity n Ainv E) i
  · exact infNorm_nonneg _

/-- The displayed normalized upper bound in Higham equation (7.25).  The
denominator is written exactly as in the source; `infNorm_absMatrix` identifies
it with `‖A⁻¹‖∞`. -/
theorem higham7_25_inverseLinearized_ratio_le
    {n : ℕ} (hn : 0 < n)
    (Ainv E ΔA : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hΔ : Higham7_25AdmissiblePerturbation E ΔA) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
        infNorm Ainv ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  rw [infNorm_absMatrix hn Ainv]
  exact div_le_div_of_nonneg_right
    (higham7_25_inverseLinearizedChange_infNorm_le n Ainv E ΔA hE hΔ)
    (infNorm_nonneg Ainv)

/-- The source equality hypothesis `|A⁻¹| = D₁ A⁻¹ D₂`, with
`D₁,D₂` diagonal sign matrices. -/
def Higham7_25InverseSignEquivalent
    {n : ℕ} (Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∃ r c : Fin n → ℝ,
    (∀ i : Fin n, r i ^ 2 = 1) ∧
      (∀ j : Fin n, c j ^ 2 = 1) ∧
      ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j

lemma higham7_abs_eq_one_of_sq_eq_one {x : ℝ} (hx : x ^ 2 = 1) :
    |x| = 1 := by
  have habsSq : |x| ^ 2 = 1 := by
    simpa [sq_abs] using hx
  nlinarith [abs_nonneg x]

/-- The perturbation that realizes equality in (7.25) under sign
equivalence. -/
def higham7_25_signAttainingPerturbation
    {n : ℕ} (E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => c i * E i j * r j

lemma higham7_25_signAttainingPerturbation_admissible
    {n : ℕ} (E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1) :
    Higham7_25AdmissiblePerturbation E
      (higham7_25_signAttainingPerturbation E r c) := by
  intro i j
  rw [show |higham7_25_signAttainingPerturbation E r c i j| = E i j by
    simp [higham7_25_signAttainingPerturbation, abs_mul,
      higham7_abs_eq_one_of_sq_eq_one (hr j),
      higham7_abs_eq_one_of_sq_eq_one (hc i), abs_of_nonneg (hE i j)]]

/-- The sign perturbation makes every triangle inequality in the derivative
bound an equality. -/
theorem higham7_25_signAttainingPerturbation_abs_eq
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1)
    (hsign : ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j) :
    ∀ i j : Fin n,
      |higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c) i j| =
        higham7_25_inverseSensitivity n Ainv E i j := by
  intro i j
  have hleft : ∀ k : Fin n,
      Ainv i k * c k = r i * |Ainv i k| := by
    intro k
    calc
      Ainv i k * c k = r i ^ 2 * (Ainv i k * c k) := by
        rw [hr i]
        ring
      _ = r i * (r i * Ainv i k * c k) := by ring
      _ = r i * |Ainv i k| := by rw [← hsign i k]
  have hright : ∀ l : Fin n,
      r l * Ainv l j = |Ainv l j| * c j := by
    intro l
    calc
      r l * Ainv l j = (r l * Ainv l j) * c j ^ 2 := by
        rw [hc j]
        ring
      _ = (r l * Ainv l j * c j) * c j := by ring
      _ = |Ainv l j| * c j := by rw [← hsign l j]
  have hcore :
      matMul n
          (matMul n Ainv (higham7_25_signAttainingPerturbation E r c))
          Ainv i j =
        r i * higham7_25_inverseSensitivity n Ainv E i j * c j := by
    simp only [matMul, higham7_25_signAttainingPerturbation,
      higham7_25_inverseSensitivity, absMatrix]
    calc
      ∑ l : Fin n, (∑ k : Fin n, Ainv i k * (c k * E k l * r l)) * Ainv l j =
          ∑ l : Fin n,
            (r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l) * Ainv l j := by
        apply Finset.sum_congr rfl
        intro l _
        congr 1
        calc
          ∑ k : Fin n, Ainv i k * (c k * E k l * r l) =
              ∑ k : Fin n, r i * (|Ainv i k| * E k l) * r l := by
            apply Finset.sum_congr rfl
            intro k _
            rw [show Ainv i k * (c k * E k l * r l) =
                (Ainv i k * c k) * E k l * r l by ring,
              hleft k]
            ring
          _ = r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ l : Fin n,
          r i * ((∑ k : Fin n, |Ainv i k| * E k l) * |Ainv l j|) * c j := by
        apply Finset.sum_congr rfl
        intro l _
        rw [show
            (r i * (∑ k : Fin n, |Ainv i k| * E k l) * r l) * Ainv l j =
              r i * (∑ k : Fin n, |Ainv i k| * E k l) *
                (r l * Ainv l j) by ring,
          hright l]
        ring
      _ = r i *
          (∑ l : Fin n,
            (∑ k : Fin n, |Ainv i k| * E k l) * |Ainv l j|) * c j := by
        rw [Finset.mul_sum, Finset.sum_mul]
  rw [higham7_25_inverseLinearizedChange, hcore, abs_neg,
    abs_mul, abs_mul,
    higham7_abs_eq_one_of_sq_eq_one (hr i),
    higham7_abs_eq_one_of_sq_eq_one (hc j),
    abs_of_nonneg (higham7_25_inverseSensitivity_nonneg n Ainv E hE i j)]
  ring

/-- Equality of matrix infinity norms for the sign-attaining perturbation. -/
theorem higham7_25_signAttainingPerturbation_infNorm_eq
    {n : ℕ} (hn : 0 < n)
    (Ainv E : Fin n → Fin n → ℝ) (r c : Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hr : ∀ i : Fin n, r i ^ 2 = 1)
    (hc : ∀ j : Fin n, c j ^ 2 = 1)
    (hsign : ∀ i j : Fin n, |Ainv i j| = r i * Ainv i j * c j) :
    infNorm (higham7_25_inverseLinearizedChange n Ainv
        (higham7_25_signAttainingPerturbation E r c)) =
      infNorm (higham7_25_inverseSensitivity n Ainv E) := by
  have habsMatrix :
      absMatrix n (higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c)) =
        higham7_25_inverseSensitivity n Ainv E := by
    funext i j
    exact higham7_25_signAttainingPerturbation_abs_eq
      Ainv E r c hE hr hc hsign i j
  calc
    infNorm (higham7_25_inverseLinearizedChange n Ainv
        (higham7_25_signAttainingPerturbation E r c)) =
        infNorm (absMatrix n (higham7_25_inverseLinearizedChange n Ainv
          (higham7_25_signAttainingPerturbation E r c))) :=
      (infNorm_absMatrix hn _).symm
    _ = infNorm (higham7_25_inverseSensitivity n Ainv E) := by
      rw [habsMatrix]

/-- Unit-ball values of the matrix-infinity norm of the inversion derivative.
This is the standard first-order characterization of the source limit
defining `μ_E(A)` in equation (7.25). -/
def Higham7_25InverseLinearizedConditionSet
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) : Set ℝ :=
  {q | ∃ ΔA : Fin n → Fin n → ℝ,
    Higham7_25AdmissiblePerturbation E ΔA ∧
      q = infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
        infNorm Ainv}

/-- Matrix-infinity relative condition number of inversion in the componentwise
perturbation direction `E`, expressed through the derivative unit ball. -/
noncomputable def higham7_25_inverseLinearizedCondition
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) : ℝ :=
  sSup (Higham7_25InverseLinearizedConditionSet Ainv E)

/-- Upper-bound half of equation (7.25), now at the actual derivative
condition-number supremum. -/
theorem higham7_25_inverseLinearizedCondition_le
    {n : ℕ} (hn : 0 < n) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    higham7_25_inverseLinearizedCondition Ainv E ≤
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  let S : Set ℝ := Higham7_25InverseLinearizedConditionSet Ainv E
  let K : ℝ := infNorm (higham7_25_inverseSensitivity n Ainv E) /
    infNorm (absMatrix n Ainv)
  let Δzero : Fin n → Fin n → ℝ := 0
  let qzero : ℝ :=
    infNorm (higham7_25_inverseLinearizedChange n Ainv Δzero) / infNorm Ainv
  have hΔzero : Higham7_25AdmissiblePerturbation E Δzero := by
    intro i j
    simpa [Δzero] using hE i j
  have hqzero : qzero ∈ S := by
    exact ⟨Δzero, hΔzero, rfl⟩
  have hupper : ∀ q : ℝ, q ∈ S → q ≤ K := by
    intro q hq
    rcases hq with ⟨ΔA, hΔ, rfl⟩
    exact higham7_25_inverseLinearized_ratio_le hn Ainv E ΔA hE hΔ
  change sSup S ≤ K
  exact csSup_le ⟨qzero, hqzero⟩ hupper

/-- Under `|A⁻¹| = D₁ A⁻¹ D₂`, the sign perturbation belongs to
the unit ball and attains the displayed right-hand side of (7.25). -/
theorem higham7_25_inverseLinearizedCondition_eq_of_signEquivalent
    {n : ℕ} (hn : 0 < n) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hsign : Higham7_25InverseSignEquivalent Ainv) :
    higham7_25_inverseLinearizedCondition Ainv E =
      infNorm (higham7_25_inverseSensitivity n Ainv E) /
        infNorm (absMatrix n Ainv) := by
  rcases hsign with ⟨r, c, hr, hc, hentries⟩
  let S : Set ℝ := Higham7_25InverseLinearizedConditionSet Ainv E
  let K : ℝ := infNorm (higham7_25_inverseSensitivity n Ainv E) /
    infNorm (absMatrix n Ainv)
  let ΔA : Fin n → Fin n → ℝ :=
    higham7_25_signAttainingPerturbation E r c
  have hΔ : Higham7_25AdmissiblePerturbation E ΔA :=
    higham7_25_signAttainingPerturbation_admissible E r c hE hr hc
  have hratio :
      infNorm (higham7_25_inverseLinearizedChange n Ainv ΔA) /
          infNorm Ainv = K := by
    rw [higham7_25_signAttainingPerturbation_infNorm_eq
      hn Ainv E r c hE hr hc hentries]
    exact congrArg
      (fun d : ℝ => infNorm (higham7_25_inverseSensitivity n Ainv E) / d)
      (infNorm_absMatrix hn Ainv).symm
  have hKmem : K ∈ S := ⟨ΔA, hΔ, hratio.symm⟩
  have hupper : ∀ q : ℝ, q ∈ S → q ≤ K := by
    intro q hq
    rcases hq with ⟨Δ, hΔ', rfl⟩
    exact higham7_25_inverseLinearized_ratio_le hn Ainv E Δ hE hΔ'
  have hbdd : BddAbove S := ⟨K, hupper⟩
  change sSup S = K
  exact le_antisymm (csSup_le ⟨K, hKmem⟩ hupper)
    (le_csSup hbdd hKmem)

/-- Higham equation (7.25), source-facing endpoint.  `Ainv` is required to be
the genuine inverse of `A`; the derivative condition is bounded by the
printed ratio, and the book's diagonal-sign hypothesis upgrades that bound to
equality. -/
theorem higham7_25_source_inverseCondition_upper_and_sign_equality
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    IsInverse n A Ainv ∧
      higham7_25_inverseLinearizedCondition Ainv E ≤
        infNorm (higham7_25_inverseSensitivity n Ainv E) /
          infNorm (absMatrix n Ainv) ∧
      (Higham7_25InverseSignEquivalent Ainv →
        higham7_25_inverseLinearizedCondition Ainv E =
          infNorm (higham7_25_inverseSensitivity n Ainv E) /
            infNorm (absMatrix n Ainv)) := by
  exact ⟨hInv, higham7_25_inverseLinearizedCondition_le hn Ainv E hE,
    higham7_25_inverseLinearizedCondition_eq_of_signEquivalent
      hn Ainv E hE⟩

/-! ## Chapter 7, equation (7.26): componentwise distance to singularity -/

/-- The nonnegative matrix `|A⁻¹|E` controlling componentwise distance to
singularity in equation (7.26). -/
noncomputable def higham7_26_distanceMajorant
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (absMatrix n Ainv) E

/-- Real value of the complexified algebraic spectral radius used in (7.26). -/
noncomputable def higham7_26_spectralRadius
    {n : ℕ} (M : Fin n → Fin n → ℝ) : ℝ :=
  (spectralRadius ℂ
    (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M)).toReal

/-- A feasible componentwise singularity radius.  The nonzero right-kernel
vector is equivalent to singularity but is retained explicitly because it is
the useful source witness for both halves of (7.26). -/
def Higham7_26FeasibleSingularRadius
    {n : ℕ} (A E : Fin n → Fin n → ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∃ ΔA : Fin n → Fin n → ℝ, ∃ x : Fin n → ℝ,
      x ≠ 0 ∧
        (∀ i j : Fin n, |ΔA i j| ≤ ε * E i j) ∧
        matMulVec n (fun i j => A i j + ΔA i j) x = 0

/-- `d` is the componentwise distance `d_E(A)` when it is the least feasible
singularity radius.  This mirrors the source's `min` definition. -/
def IsHigham7_26ComponentwiseDistance
    {n : ℕ} (A E : Fin n → Fin n → ℝ) (d : ℝ) : Prop :=
  IsLeast { ε : ℝ | Higham7_26FeasibleSingularRadius A E ε } d

lemma higham7_26_distanceMajorant_nonneg
    (n : ℕ) (Ainv E : Fin n → Fin n → ℝ)
    (hE : ∀ i j : Fin n, 0 ≤ E i j) :
    ∀ i j : Fin n, 0 ≤ higham7_26_distanceMajorant n Ainv E i j :=
  ch7_matMul_nonneg n (absMatrix n Ainv) E
    (by intro i j; exact abs_nonneg _) hE

section Higham7_26MatrixOperatorNorm

open scoped Matrix.Norms.Operator

/-- The algebraic spectral radius used in (7.26) is finite. -/
lemma higham7_26_spectralRadius_ne_top
    {n : ℕ} (hn : 0 < n) (M : Fin n → Fin n → ℝ) :
    spectralRadius ℂ
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) ≠ ⊤ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let C : Matrix (Fin n) (Fin n) ℂ := realRectToCMatrix M
  letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hcomplete : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  have hbound :=
    @spectrum.spectralRadius_le_nnnorm ℂ
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance inferInstance
      hcomplete inferInstance C
  change spectralRadius ℂ C ≠ ⊤
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hbound

end Higham7_26MatrixOperatorNorm

/-- Every actual singular perturbation obeys the reciprocal-spectral-radius
lower bound in (7.26). -/
theorem higham7_26_feasibleRadius_ge_reciprocal_spectralRadius
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (ε : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hε : Higham7_26FeasibleSingularRadius A E ε) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ ε := by
  rcases hε with ⟨hεnonneg, ΔA, x, hxne, hΔ, hker⟩
  let M : Fin n → Fin n → ℝ :=
    higham7_26_distanceMajorant n Ainv E
  let v : Fin n → ℝ := fun i => |x i|
  have hAx : ∀ i : Fin n,
      matMulVec n A x i = -matMulVec n ΔA x i := by
    intro i
    have hi := congrFun hker i
    have hadd : matMulVec n (fun i j => A i j + ΔA i j) x i =
        matMulVec n A x i + matMulVec n ΔA x i := by
      unfold matMulVec
      simp [add_mul, Finset.sum_add_distrib]
    rw [hadd] at hi
    simpa using eq_neg_of_add_eq_zero_left hi
  have hleft : matMulVec n Ainv (matMulVec n A x) = x := by
    simpa [matMulVec, rectMatMulVec] using
      rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 x
  have hxrepr : ∀ i : Fin n,
      x i = -matMulVec n Ainv (matMulVec n ΔA x) i := by
    intro i
    calc
      x i = matMulVec n Ainv (matMulVec n A x) i :=
        congrFun hleft.symm i
      _ = matMulVec n Ainv (fun k => -matMulVec n ΔA x k) i := by
        congr 1
        funext k
        exact hAx k
      _ = -matMulVec n Ainv (matMulVec n ΔA x) i := by
        unfold matMulVec
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hΔx : ∀ k : Fin n,
      |matMulVec n ΔA x k| ≤
        ε * ∑ j : Fin n, E k j * |x j| := by
    intro k
    calc
      |matMulVec n ΔA x k| ≤ ∑ j : Fin n, |ΔA k j| * |x j| :=
        abs_matMulVec_le n ΔA x k
      _ ≤ ∑ j : Fin n, (ε * E k j) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hΔ k j) (abs_nonneg _)
      _ = ε * ∑ j : Fin n, E k j * |x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsub : ∀ i : Fin n,
      v i ≤ ε * matMulVec n M v i := by
    intro i
    calc
      v i = |matMulVec n Ainv (matMulVec n ΔA x) i| := by
        dsimp [v]
        rw [hxrepr i, abs_neg]
      _ ≤ ∑ k : Fin n, |Ainv i k| * |matMulVec n ΔA x k| :=
        abs_matMulVec_le n Ainv (matMulVec n ΔA x) i
      _ ≤ ∑ k : Fin n,
          |Ainv i k| * (ε * ∑ j : Fin n, E k j * |x j|) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hΔx k) (abs_nonneg _)
      _ = ε * matMulVec n (absMatrix n Ainv) (matMulVec n E v) i := by
        simp only [matMulVec]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [v, absMatrix]
        ring
      _ = ε * matMulVec n M v i := by
        rw [← matMulVec_matMul n (absMatrix n Ainv) E v i]
        rfl
  have hvne : v ≠ 0 := by
    intro hv
    apply hxne
    funext i
    have hi := congrFun hv i
    dsimp [v] at hi
    exact abs_eq_zero.mp hi
  have hεpos : 0 < ε := by
    apply lt_of_le_of_ne hεnonneg
    intro hzero
    have hεzero : ε = 0 := hzero.symm
    apply hvne
    funext i
    have hi := hsub i
    rw [hεzero, zero_mul] at hi
    exact le_antisymm hi (abs_nonneg _)
  have hscaled : ∀ i : Fin n,
      (1 / ε) * v i ≤ matMulVec n M v i := by
    intro i
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hεpos).2
    simpa [mul_comm] using hsub i
  have hspectral :
      ENNReal.ofReal (1 / ε) ≤
        spectralRadius ℂ
          (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M) :=
    ch7_matrix_spectralRadius_ge_of_nonzero_nonneg_right_subeigenvector
      hn M (1 / ε) v
      (by simpa [M] using higham7_26_distanceMajorant_nonneg n Ainv E hE)
      (one_div_nonneg.mpr hεnonneg)
      (by intro i; exact abs_nonneg _) hvne hscaled
  have hspectralReal :
      1 / ε ≤ higham7_26_spectralRadius M := by
    have h := (ENNReal.toReal_le_toReal
      (by simp) (higham7_26_spectralRadius_ne_top hn M)).2 hspectral
    change 1 / ε ≤
      (spectralRadius ℂ
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix M)).toReal
    rw [← ENNReal.toReal_ofReal (one_div_nonneg.mpr hεnonneg)]
    exact h
  have hρpos : 0 < higham7_26_spectralRadius M :=
    lt_of_lt_of_le (one_div_pos.mpr hεpos) hspectralReal
  change 1 / higham7_26_spectralRadius M ≤ ε
  apply (div_le_iff₀ hρpos).2
  calc
    1 = ε * (1 / ε) := by field_simp
    _ ≤ ε * higham7_26_spectralRadius M :=
      mul_le_mul_of_nonneg_left hspectralReal (le_of_lt hεpos)
    _ = ε * higham7_26_spectralRadius M := rfl

/-- Lower-bound half of source equation (7.26) for the actual minimum
componentwise singularity radius. -/
theorem higham7_26_componentwiseDistance_ge_reciprocal_spectralRadius
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ d :=
  higham7_26_feasibleRadius_ge_reciprocal_spectralRadius
    hn A Ainv E d hInv hE hd.1

/-- The universal factor in Rump's upper estimate in equation (7.26). -/
noncomputable def higham7_26_rumpFactor (n : ℕ) : ℝ :=
  (3 + 2 * Real.sqrt 2) * (n : ℝ)

/-- The linear-algebra output of the hard Rump cycle/sign-real-spectral-radius
argument behind the upper half of (7.26).  Unlike a singular-perturbation or
distance-bound premise, this exposes the signed perturbation matrix and its
ordinary real eigenpair.  Rump's Theorems 3.2 and 4.4 construct precisely this
certificate (after absorbing the row signature into a column signature). -/
structure Higham7_26RumpEigenpairCertificate
    {n : ℕ} (Ainv E : Fin n → Fin n → ℝ) where
  F : Fin n → Fin n → ℝ
  x : Fin n → ℝ
  lam : ℝ
  x_ne : x ≠ 0
  lam_pos : 0 < lam
  F_bound : ∀ i j : Fin n, |F i j| ≤ E i j
  eigenpair :
    matMulVec n Ainv (matMulVec n F x) = fun i => lam * x i
  spectral_fraction_le_lam :
    higham7_26_spectralRadius
        (higham7_26_distanceMajorant n Ainv E) /
          higham7_26_rumpFactor n ≤ lam

/-- A Rump signed-eigenpair certificate produces an actual singular
componentwise perturbation of radius `1 / λ`. -/
theorem higham7_26_feasibleRadius_of_rumpEigenpairCertificate
    {n : ℕ} (A Ainv E : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A Ainv)
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    Higham7_26FeasibleSingularRadius A E (1 / c.lam) := by
  let ΔA : Fin n → Fin n → ℝ := fun i j => -(1 / c.lam) * c.F i j
  refine ⟨one_div_nonneg.mpr (le_of_lt c.lam_pos), ΔA, c.x, c.x_ne, ?_, ?_⟩
  · intro i j
    dsimp [ΔA]
    calc
      |-(1 / c.lam) * c.F i j| = (1 / c.lam) * |c.F i j| := by
        rw [abs_mul, abs_neg, abs_of_nonneg
          (one_div_nonneg.mpr (le_of_lt c.lam_pos))]
      _ ≤ (1 / c.lam) * E i j :=
        mul_le_mul_of_nonneg_left (c.F_bound i j)
          (one_div_nonneg.mpr (le_of_lt c.lam_pos))
  · have hright : ∀ y : Fin n → ℝ,
        matMulVec n A (matMulVec n Ainv y) = y := by
      intro y
      simpa [matMulVec, rectMatMulVec] using
        rectMatMulVec_left_inverse_of_IsLeftInverse
          (show IsLeftInverse n Ainv A from hInv.2) y
    have hFx : ∀ i : Fin n,
        matMulVec n c.F c.x i = c.lam * matMulVec n A c.x i := by
      intro i
      calc
        matMulVec n c.F c.x i =
            matMulVec n A (matMulVec n Ainv (matMulVec n c.F c.x)) i :=
          congrFun (hright (matMulVec n c.F c.x)).symm i
        _ = matMulVec n A (fun j => c.lam * c.x j) i := by
          rw [c.eigenpair]
        _ = c.lam * matMulVec n A c.x i := by
          unfold matMulVec
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    funext i
    calc
      matMulVec n (fun i j => A i j + ΔA i j) c.x i =
          matMulVec n A c.x i + matMulVec n ΔA c.x i := by
        unfold matMulVec
        simp [add_mul, Finset.sum_add_distrib]
      _ = matMulVec n A c.x i +
          (-(1 / c.lam) * matMulVec n c.F c.x i) := by
        congr 1
        unfold matMulVec
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [ΔA]
        ring
      _ = 0 := by
        rw [hFx i]
        field_simp [ne_of_gt c.lam_pos]
        ring

/-- Upper half of source equation (7.26), reduced to Rump's genuine signed
eigenpair output rather than to a target-equivalent distance premise. -/
theorem higham7_26_componentwiseDistance_le_rumpBound_of_eigenpairCertificate
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hρ : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E))
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    d ≤ higham7_26_rumpFactor n /
      higham7_26_spectralRadius
        (higham7_26_distanceMajorant n Ainv E) := by
  have hK : 0 < higham7_26_rumpFactor n := by
    dsimp [higham7_26_rumpFactor]
    positivity
  have hfeasible :=
    higham7_26_feasibleRadius_of_rumpEigenpairCertificate A Ainv E hInv c
  have hdle : d ≤ 1 / c.lam := hd.2 hfeasible
  refine hdle.trans ?_
  apply (div_le_div_iff₀ c.lam_pos hρ).2
  have hscaled := (div_le_iff₀ hK).1 c.spectral_fraction_le_lam
  nlinarith

/-- Source-shaped two-sided equation (7.26) once Rump's cycle theorem has
supplied its signed eigenpair certificate. -/
theorem higham7_26_source_distance_sandwich_of_rumpEigenpairCertificate
    {n : ℕ} (hn : 0 < n)
    (A Ainv E : Fin n → Fin n → ℝ) (d : ℝ)
    (hInv : IsInverse n A Ainv)
    (hE : ∀ i j : Fin n, 0 ≤ E i j)
    (hd : IsHigham7_26ComponentwiseDistance A E d)
    (hρ : 0 < higham7_26_spectralRadius
      (higham7_26_distanceMajorant n Ainv E))
    (c : Higham7_26RumpEigenpairCertificate Ainv E) :
    1 / higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) ≤ d ∧
      d ≤ higham7_26_rumpFactor n /
        higham7_26_spectralRadius
          (higham7_26_distanceMajorant n Ainv E) :=
  ⟨higham7_26_componentwiseDistance_ge_reciprocal_spectralRadius
      hn A Ainv E d hInv hE hd,
    higham7_26_componentwiseDistance_le_rumpBound_of_eigenpairCertificate
      hn A Ainv E d hInv hd hρ c⟩

/-! ## Chapter 8, section 8.3: bidiagonal comparison inverses -/

/-- An upper-triangular matrix is upper bidiagonal when entries more than one
place above the diagonal vanish. -/
def IsUpperBidiagonal (n : ℕ) (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val + 1 < j.val → U i j = 0

/-- Higham, 2nd ed., section 8.3, p. 148: for a nonsingular upper bidiagonal
matrix `U`, the absolute value of its inverse is exactly the inverse of its
comparison matrix, `|U⁻¹| = M(U)⁻¹`.

The proof strengthens the first inequality of Theorem 8.12.  In the inverse
recurrence every row has at most one off-diagonal contribution, so the triangle
inequality used for a general triangular matrix is an equality. -/
theorem higham8_bidiagonal_abs_inv_eq_comparison_inv
    (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    ∀ i j : Fin n, |U_inv i j| = M_inv i j := by
  have hU_inv_ut := inv_upper_tri n U U_inv hUT hU_diag hInv.1
  have hM_ut : ∀ i j : Fin n, j.val < i.val → comparisonMatrix n U i j = 0 := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      omega
    simp [comparisonMatrix, hne, hUT i j hij]
  have hM_diag : ∀ i : Fin n, comparisonMatrix n U i i ≠ 0 := by
    intro i
    simpa [comparisonMatrix] using hU_diag i
  have hM_inv_ut := inv_upper_tri n (comparisonMatrix n U) M_inv
    hM_ut hM_diag hMInv.1
  have hM_nonneg : ∀ i j : Fin n, 0 ≤ M_inv i j := by
    apply upper_tri_mmatrix_inv_nonneg n (comparisonMatrix n U) M_inv
    · exact hM_ut
    · intro i
      simpa [comparisonMatrix] using (abs_pos.mpr (hU_diag i))
    · intro i j hij
      have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp [comparisonMatrix, hne]
    · exact hMInv.2
    · exact hM_inv_ut
  suffices h : ∀ d : ℕ, ∀ i j : Fin n,
      j.val - i.val ≤ d → i.val ≤ j.val → |U_inv i j| = M_inv i j by
    intro i j
    by_cases hij : i.val ≤ j.val
    · exact h (j.val - i.val) i j le_rfl hij
    · have hji : j.val < i.val := by omega
      rw [hU_inv_ut i j hji, hM_inv_ut i j hji, abs_zero]
  intro d
  induction d with
  | zero =>
      intro i j hdist hij
      have hij_eq : i = j := Fin.ext (by omega)
      subst j
      have hUdiag := inv_diag_entry n U U_inv hUT hU_diag hInv.1 hU_inv_ut i
      have hMdiag := inv_diag_entry n (comparisonMatrix n U) M_inv
        hM_ut hM_diag hMInv.1 hM_inv_ut i
      rw [hUdiag, hMdiag, abs_div, abs_one]
      simp [comparisonMatrix]
  | succ d ih =>
      intro i j hdist hij
      by_cases heq : i = j
      · subst j
        exact ih i i (by omega) le_rfl
      · have hij_lt : i.val < j.val := by omega
        let ip1 : Fin n := ⟨i.val + 1, by omega⟩
        let S : Finset (Fin n) :=
          Finset.univ.filter (fun k : Fin n => i.val < k.val ∧ k.val ≤ j.val)
        have hip1_mem : ip1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · simp [ip1]
          · change i.val + 1 ≤ j.val
            exact Nat.succ_le_iff.mpr hij_lt
        have hsumU :
            (∑ k ∈ S, U i k * U_inv k j) = U i ip1 * U_inv ip1 j := by
          apply Finset.sum_eq_single ip1
          · intro k hk hki
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hfar : i.val + 1 < k.val := by
              have hneval : k.val ≠ i.val + 1 := by
                intro hkval
                apply hki
                exact Fin.ext hkval
              omega
            rw [hUB i k hfar, zero_mul]
          · exact fun hnot => (hnot hip1_mem).elim
        have hsumM :
            (∑ k ∈ S, comparisonMatrix n U i k * M_inv k j) =
              comparisonMatrix n U i ip1 * M_inv ip1 j := by
          apply Finset.sum_eq_single ip1
          · intro k hk hki
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            have hfar : i.val + 1 < k.val := by
              have hneval : k.val ≠ i.val + 1 := by
                intro hkval
                apply hki
                exact Fin.ext hkval
              omega
            have hzero := hUB i k hfar
            have hik : i ≠ k := by
              intro h
              subst k
              omega
            simp [comparisonMatrix, hik, hzero]
          · exact fun hnot => (hnot hip1_mem).elim
        have hrecU := inv_recurrence n U U_inv hUT hU_diag hInv.2
          hU_inv_ut i j hij_lt
        have hrecM := inv_recurrence n (comparisonMatrix n U) M_inv hM_ut
          hM_diag hMInv.2 hM_inv_ut i j hij_lt
        change U i i * U_inv i j + (∑ k ∈ S, U i k * U_inv k j) = 0 at hrecU
        change comparisonMatrix n U i i * M_inv i j +
          (∑ k ∈ S, comparisonMatrix n U i k * M_inv k j) = 0 at hrecM
        rw [hsumU] at hrecU
        rw [hsumM] at hrecM
        have hipdist : j.val - ip1.val ≤ d := by
          change j.val - (i.val + 1) ≤ d
          omega
        have hip_le : ip1.val ≤ j.val := by
          dsimp [ip1]
          omega
        have ih_abs : |U_inv ip1 j| = M_inv ip1 j :=
          ih ip1 j hipdist hip_le
        have hUii_abs_pos : 0 < |U i i| := abs_pos.mpr (hU_diag i)
        have hUeq : U_inv i j = -(U i ip1 * U_inv ip1 j) / U i i := by
          field_simp [hU_diag i]
          linarith
        have hMeq : M_inv i j =
            |U i ip1| * M_inv ip1 j / |U i i| := by
          have hii : comparisonMatrix n U i i = |U i i| := by
            simp [comparisonMatrix]
          have hip : comparisonMatrix n U i ip1 = -|U i ip1| := by
            have hne : i ≠ ip1 := by
              intro h
              have hval := congrArg Fin.val h
              dsimp [ip1] at hval
              omega
            simp [comparisonMatrix, hne]
          rw [hii, hip] at hrecM
          field_simp [ne_of_gt hUii_abs_pos]
          linarith
        rw [hUeq, abs_div, abs_neg, abs_mul, ih_abs, hMeq]

/-- Matrix form of `higham8_bidiagonal_abs_inv_eq_comparison_inv`. -/
theorem higham8_bidiagonal_absMatrix_inv_eq_comparison_inv
    (n : ℕ) (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    absMatrix n U_inv = M_inv := by
  funext i j
  exact higham8_bidiagonal_abs_inv_eq_comparison_inv
    n U U_inv M_inv hUT hUB hU_diag hInv hMInv i j

/-- For an upper bidiagonal matrix, Algorithm 8.13 is exact rather than merely
an upper bound: its comparison-inverse output is `‖U⁻¹‖∞` itself. -/
theorem higham8_bidiagonal_algorithm8_13_mu_eq_inverse_infNorm
    (n : ℕ) (hn : 0 < n)
    (U U_inv M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : IsInverse n U U_inv)
    (hMInv : IsInverse n (comparisonMatrix n U) M_inv) :
    higham8_13_mu M_inv = infNorm U_inv := by
  unfold higham8_13_mu
  rw [← higham8_bidiagonal_absMatrix_inv_eq_comparison_inv
    n U U_inv M_inv hUT hUB hU_diag hInv hMInv]
  exact infNorm_absMatrix hn U_inv

/-- In the bidiagonal case the comparison solve used by Algorithm 8.13 has
only one dependency per row.  This is the exact descending two-term
recurrence that gives the source's `O(n)` computation. -/
theorem higham8_bidiagonal_algorithm8_13_two_term_recurrence
    (n : ℕ) (U M_inv : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUB : IsUpperBidiagonal n U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hM_RInv : IsRightInverse n (comparisonMatrix n U) M_inv)
    (i : Fin n) :
    |U i i| * higham8_13_y M_inv i =
      1 + if hi : i.val + 1 < n then
        |U i ⟨i.val + 1, hi⟩| * higham8_13_y M_inv ⟨i.val + 1, hi⟩
      else 0 := by
  have hrec := higham8_13_comparison_inverse_row_recurrence
    n U M_inv hUT hU_diag hM_RInv i
  rw [hrec]
  split_ifs with hi
  · let ip1 : Fin n := ⟨i.val + 1, hi⟩
    let S : Finset (Fin n) :=
      Finset.univ.filter (fun j : Fin n => i.val < j.val)
    have hip1_mem : ip1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < i.val + 1
      omega
    have hsum :
        (∑ j ∈ S, |U i j| * higham8_13_y M_inv j) =
          |U i ip1| * higham8_13_y M_inv ip1 := by
      apply Finset.sum_eq_single ip1
      · intro j hj hne
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hfar : i.val + 1 < j.val := by
          have hval : j.val ≠ i.val + 1 := by
            intro h
            apply hne
            exact Fin.ext h
          omega
        rw [hUB i j hfar, abs_zero, zero_mul]
      · exact fun hnot => (hnot hip1_mem).elim
    simpa [S, ip1] using hsum
  · have hfilter_empty :
        Finset.univ.filter (fun j : Fin n => i.val < j.val) = ∅ := by
      ext j
      simp
      omega
    rw [hfilter_empty]
    simp

/-! ## Chapter 8, equation (8.10): QR with column pivoting -/

/-- At one executed column-pivoted Householder stage, the squared diagonal
pivot dominates the squared 2-norm of every later active column.  This is the
strong full-column form underlying Higham's (8.10).

The maximality premise is not assumed: `colPivotSwap` is the repository's
executed maximal-column selection.  The only structural premise says that the
exact Householder reflector has annihilated the tail of its pivot column. -/
theorem higham8_10_colPivot_stage_full_column_sq_le_pivot_sq
    {q : ℕ}
    (A : Fin (q + 1) → Fin (q + 1) → ℝ)
    (P : Fin (q + 1) → Fin (q + 1) → ℝ)
    (hP : IsOrthogonal (q + 1) P)
    (hpivotTail : ∀ i : Fin q,
      matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
        i.succ 0 = 0)
    (j : Fin q) :
    ∑ i : Fin (q + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      (matMulRect (q + 1) (q + 1) (q + 1) P
        (Wave20.colPivotSwap A) 0 0) ^ 2 := by
  let R : Fin (q + 1) → Fin (q + 1) → ℝ :=
    matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
  have hjmax : columnFrob R j.succ ≤ columnFrob R 0 := by
    calc
      columnFrob R j.succ = columnFrob (Wave20.colPivotSwap A) j.succ := by
        exact columnFrob_orthogonal_left P (Wave20.colPivotSwap A) hP j.succ
      _ ≤ columnFrob (Wave20.colPivotSwap A) 0 :=
        Wave20.columnFrob_colPivotSwap_zero_max A j.succ
      _ = columnFrob R 0 := by
        symm
        exact columnFrob_orthogonal_left P (Wave20.colPivotSwap A) hP 0
  have hsq : columnFrob R j.succ ^ 2 ≤ columnFrob R 0 ^ 2 := by
    nlinarith [columnFrob_nonneg R j.succ, columnFrob_nonneg R 0]
  have hpivotSq : columnFrob R 0 ^ 2 = R 0 0 ^ 2 := by
    have htail : ∀ i : Fin q, R i.succ 0 = 0 := by
      intro i
      exact hpivotTail i
    rw [columnFrob_eq_vecNorm2, vecNorm2_sq]
    unfold vecNorm2Sq
    rw [Fin.sum_univ_succ]
    simp [htail]
  have hjSq : columnFrob R j.succ ^ 2 = ∑ i : Fin (q + 1), (R i j.succ) ^ 2 := by
    rw [columnFrob_eq_vecNorm2, vecNorm2_sq]
    rfl
  rw [hjSq, hpivotSq] at hsq
  exact hsq

/-- Higham (8.10), in the coordinates of an arbitrary active pivot stage:
for later active column `j+1`, the pivot square dominates the partial column
sum through row `j+1`.  The preceding theorem proves the stronger bound with
the whole active column, so this is an immediate nonnegative sub-sum. -/
theorem higham8_10_colPivot_stage_partial_column_sq_le_pivot_sq
    {q : ℕ}
    (A : Fin (q + 1) → Fin (q + 1) → ℝ)
    (P : Fin (q + 1) → Fin (q + 1) → ℝ)
    (hP : IsOrthogonal (q + 1) P)
    (hpivotTail : ∀ i : Fin q,
      matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
        i.succ 0 = 0)
    (j : Fin q) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (q + 1) => i.val ≤ j.val + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      (matMulRect (q + 1) (q + 1) (q + 1) P
        (Wave20.colPivotSwap A) 0 0) ^ 2 := by
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin (q + 1) => i.val ≤ j.val + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      ∑ i : Fin (q + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) 0 0) ^ 2 :=
      higham8_10_colPivot_stage_full_column_sq_le_pivot_sq
        A P hP hpivotTail j

/-! ## Chapter 8, section 8.4: genuine fan-in asymptotics -/

/-- The bounded coefficient in the identity
`gamma_n(u) = u * higham8_18_gammaUnitCoefficient n u`. -/
noncomputable def higham8_18_gammaUnitCoefficient (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) / (1 - (n : ℝ) * u)

theorem higham8_18_gamma_eq_unit_mul_coefficient (fp : FPModel) (n : ℕ) :
    gamma fp n = fp.u * higham8_18_gammaUnitCoefficient n fp.u := by
  unfold gamma higham8_18_gammaUnitCoefficient
  ring

theorem higham8_18_gammaUnitCoefficient_continuousAt_zero (n : ℕ) :
    ContinuousAt (higham8_18_gammaUnitCoefficient n) 0 := by
  unfold higham8_18_gammaUnitCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- With the operation count fixed, `gamma_n` is uniformly `O(u)` along a
vanishing-roundoff family. -/
theorem higham8_18_gamma_family_isBigO_unit
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel) (n : ℕ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gamma (fp t) n) =O[l] (fun t => (fp t).u) := by
  have hu_refl := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hcoeff :
      (fun t => higham8_18_gammaUnitCoefficient n (fp t).u) =O[l]
        (fun _ : ι => (1 : ℝ)) := by
    simpa only [Function.comp_apply] using
      (higham8_18_gammaUnitCoefficient_continuousAt_zero n).tendsto.isBigO_one
        ℝ |>.comp_tendsto hu
  simpa only [higham8_18_gamma_eq_unit_mul_coefficient, mul_one] using
    hu_refl.mul hcoeff

/-- The named higher-order coefficient in the literal seven-operation fan-in
bound is genuinely `O(u²)`, uniformly along every fixed-dimension family whose
unit roundoff tends to zero.  This supplies the Landau statement that was
previously only described in the declaration's prose. -/
theorem higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel) (n : ℕ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => higham8_18_fanIn7CoefficientRemainder (fp t) n) =O[l]
      (fun t => (fp t).u ^ 2) := by
  let u : ι → ℝ := fun t => (fp t).u
  let g : ι → ℝ := fun t => gamma (fp t) n
  have hu_refl : u =O[l] u := Asymptotics.isBigO_refl u l
  have hcoeff :
      (fun t => higham8_18_gammaUnitCoefficient n (u t)) =O[l]
        (fun _ : ι => (1 : ℝ)) := by
    simpa only [Function.comp_apply, u] using
      (higham8_18_gammaUnitCoefficient_continuousAt_zero n).tendsto.isBigO_one
        ℝ |>.comp_tendsto hu
  have hg : g =O[l] u := by
    have hproduct := hu_refl.mul hcoeff
    simpa only [g, u, higham8_18_gamma_eq_unit_mul_coefficient, mul_one]
      using hproduct
  have hu_one : u =O[l] (fun _ : ι => (1 : ℝ)) := hu.isBigO_one ℝ
  have hg_one : g =O[l] (fun _ : ι => (1 : ℝ)) := hg.trans hu_one
  have hg2 : (fun t => g t ^ 2) =O[l] (fun t => u t ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have hg3 : (fun t => g t ^ 3) =O[l] (fun t => u t ^ 2) := by
    convert hg2.mul hg_one using 1 <;> funext t <;> ring
  have hg4 : (fun t => g t ^ 4) =O[l] (fun t => u t ^ 2) := by
    convert hg3.mul hg_one using 1 <;> funext t <;> ring
  have hg5 : (fun t => g t ^ 5) =O[l] (fun t => u t ^ 2) := by
    convert hg4.mul hg_one using 1 <;> funext t <;> ring
  have hg6 : (fun t => g t ^ 6) =O[l] (fun t => u t ^ 2) := by
    convert hg5.mul hg_one using 1 <;> funext t <;> ring
  have hg7 : (fun t => g t ^ 7) =O[l] (fun t => u t ^ 2) := by
    convert hg6.mul hg_one using 1 <;> funext t <;> ring
  have hgammaRemainder :
      (fun t => (((n : ℝ) * u t) ^ 2) / (1 - (n : ℝ) * u t)) =O[l]
        (fun t => u t ^ 2) := by
    have hproduct := (hu_refl.mul hg).const_mul_left (n : ℝ)
    convert hproduct using 1
    · funext t
      dsimp only [g, u]
      unfold gamma
      ring
    · funext t
      ring
  have hsum :=
    (((((hgammaRemainder.const_mul_left 7).add
      (hg2.const_mul_left 21)).add
      (hg3.const_mul_left 35)).add
      (hg4.const_mul_left 35)).add
      (hg5.const_mul_left 21)).add
      (hg6.const_mul_left 7) |>.add hg7
  convert hsum using 1

private theorem higham8_18_fanIn7AbsApply_nonneg (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) :
    ∀ i, 0 ≤ higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i := by
  have hmul (A B : Fin n → Fin n → ℝ)
      (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
      ∀ i j, 0 ≤ matMul n A B i j := by
    intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))
  have hmulVec (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
      (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) :
      ∀ i, 0 ≤ matMulVec n A x i := by
    intro i
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hx k))
  have habs (A : Fin n → Fin n → ℝ) :
      ∀ i j, 0 ≤ absMatrix n A i j := fun i j => abs_nonneg (A i j)
  have h76 := hmul (absMatrix n M7) (absMatrix n M6) (habs M7) (habs M6)
  have h54 := hmul (absMatrix n M5) (absMatrix n M4) (habs M5) (habs M4)
  have h7654 := hmul
    (matMul n (absMatrix n M7) (absMatrix n M6))
    (matMul n (absMatrix n M5) (absMatrix n M4)) h76 h54
  have h32 := hmul (absMatrix n M3) (absMatrix n M2) (habs M3) (habs M2)
  have h321 := hmul
    (matMul n (absMatrix n M3) (absMatrix n M2))
    (absMatrix n M1) h32 (habs M1)
  have hall := hmul
    (matMul n
      (matMul n (absMatrix n M7) (absMatrix n M6))
      (matMul n (absMatrix n M5) (absMatrix n M4)))
    (matMul n
      (matMul n (absMatrix n M3) (absMatrix n M2))
      (absMatrix n M1)) h7654 h321
  exact hmulVec _ (absVec n b) hall (fun i => abs_nonneg (b i))

/-- Family-level `(8.18)` for the literal rounded fan-in executor.  Unlike a
pointwise existential `O(u²)`, this statement has one uniform Landau constant
along the family and therefore records a genuine first-order expansion. -/
theorem higham8_18_fanIn7Executor_family_firstOrder
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n)
    (i : Fin n) :
    FamilyFirstOrderLe l (fun t => (fp t).u)
      (fun t => (7 * (n : ℝ) * (fp t).u) *
        higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i)
      (fun t =>
        |higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b i -
          higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i|) := by
  let E := higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i
  refine ⟨fun t => E * higham8_18_fanIn7CoefficientRemainder (fp t) n,
    ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg
      (higham8_18_fanIn7AbsApply_nonneg n M1 M2 M3 M4 M5 M6 M7 b i)
      (higham8_18_fanIn7CoefficientRemainder_nonneg (fp t) n (hvalid t))
  · intro t
    have h := higham8_18_fanIn7Executor_forward_first_order_remainder_bound
      (fp t) n M1 M2 M3 M4 M5 M6 M7 b (hvalid t) i
    simpa only [E, mul_comm E] using h
  · simpa only [E] using
      (higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq fp n hu).const_mul_left E

/-- Family-level `(8.15)` for the literal executor.  It upgrades the existing
named remainder split to an actual `O(u²)` residual statement.  Its leading
matrix is intentionally the honest global raw envelope; the source's sharper
five-factor leading term is obtained below from the local perturbation tree. -/
theorem higham8_15_fanIn7Executor_residual_family_firstOrder
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n)
    (hsolve :
      matMulVec n L (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b)
    (i : Fin n) :
    FamilyFirstOrderLe l (fun t => (fp t).u)
      (fun t => (7 * (n : ℝ) * (fp t).u) *
        matMulVec n (absMatrix n L)
          (higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b) i)
      (fun t =>
        |b i - matMulVec n L
          (higham8_14_fanIn7Executor (fp t) n
            M1 M2 M3 M4 M5 M6 M7 b) i|) := by
  let E : Fin n → ℝ :=
    higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b
  let R : ℝ := matMulVec n (absMatrix n L) E i
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg (L i j))
        (higham8_18_fanIn7AbsApply_nonneg n M1 M2 M3 M4 M5 M6 M7 b j))
  refine ⟨fun t => R * higham8_18_fanIn7CoefficientRemainder (fp t) n,
    ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg hR
      (higham8_18_fanIn7CoefficientRemainder_nonneg (fp t) n (hvalid t))
  · intro t
    have h := higham8_15_fanIn7Executor_residual_first_order_remainder_bound
      (fp t) n L M1 M2 M3 M4 M5 M6 M7 b (hvalid t) hsolve i
    let a : ℝ := 7 * (n : ℝ) * (fp t).u
    let r : ℝ := higham8_18_fanIn7CoefficientRemainder (fp t) n
    have hexpand :
        matMulVec n (absMatrix n L) (fun j => a * E j + r * E j) i =
          a * R + R * r := by
      calc
        matMulVec n (absMatrix n L) (fun j => a * E j + r * E j) i =
            matMulVec n (absMatrix n L) (fun j => a * E j) i +
              matMulVec n (absMatrix n L) (fun j => r * E j) i := by
                exact congrFun
                  (matMulVec_add_right n (absMatrix n L)
                    (fun j => a * E j) (fun j => r * E j)) i
        _ = a * R + r * R := by
              rw [congrFun (matMulVec_const_mul_right n (absMatrix n L) a E) i,
                congrFun (matMulVec_const_mul_right n (absMatrix n L) r E) i]
        _ = a * R + R * r := by ring
    change |b i - matMulVec n L
        (higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b) i| ≤
      (7 * (n : ℝ) * (fp t).u) * R +
        R * higham8_18_fanIn7CoefficientRemainder (fp t) n
    exact le_trans h (by simpa [a, r, E, R] using le_of_eq hexpand)
  · simpa only [R] using
      (higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq fp n hu).const_mul_left R

/-! ### The source's local perturbation expansion

The all-orders executor envelope above is deliberately too coarse to imply
the printed five-factor leading term.  The following objects instead expand
the five local perturbations in (8.14) before taking absolute values. -/

/-- The five terms of the fan-in tree that are linear in one local
perturbation.  Here `A=M₇M₆`, `B=M₅M₄`, `C=M₃M₂`, and `D=M₁`, while
`a,b,c,d,e` denote `Δ₇₆,Δ₅₄,Δ₃₂,Δ₁,Δ₇₆₅₄`. -/
noncomputable def higham8_14_fanIn7LocalLinearMatrix {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  a * B * C * D + A * b * C * D + e * C * D +
    A * B * c * D + A * B * C * d

/-- Every term omitted from the local linearization contains at least two
local perturbations.  The grouped form keeps that fact syntactically visible. -/
noncomputable def higham8_14_fanIn7LocalQuadraticRemainderMatrix {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  a * b * (C * D) + (A * B) * (c * d) +
    (a * B + A * b + e) * (c * D + C * d) +
    (a * B + A * b + e) * (c * d) +
    (a * b) * (c * D + C * d) +
    (a * b) * (c * d)

/-- Exact noncommutative expansion of the source's equation (8.14). -/
theorem higham8_14_fanIn7_local_exact_linear_quadratic_expansion {n : ℕ}
    (A B C D a b c d e : Matrix (Fin n) (Fin n) ℝ) :
    ((A + a) * (B + b) + e) * ((C + c) * (D + d)) =
      A * B * C * D +
        higham8_14_fanIn7LocalLinearMatrix A B C D a b c d e +
        higham8_14_fanIn7LocalQuadraticRemainderMatrix A B C D a b c d e := by
  unfold higham8_14_fanIn7LocalLinearMatrix
    higham8_14_fanIn7LocalQuadraticRemainderMatrix
  noncomm_ring

/-- Bridge between the chapter's explicit finite-sum multiplication and the
native `Matrix` multiplication used by the noncommutative polynomial proof. -/
theorem higham8_matMul_eq_matrix_mul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : matMul n A B = A * B := by
  ext i j
  simp [matMul, Matrix.mul_apply]

/-- Equation (8.14) itself is therefore exactly the unperturbed fan-in
product, plus its five local linear terms, plus the named cross-term
remainder. -/
theorem higham8_14_fanIn7RoundedMatrix_eq_exact_add_localLinear_add_remainder
    (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 :
      Matrix (Fin n) (Fin n) ℝ) :
    higham8_14_fanIn7RoundedMatrix n
        M1 M2 M3 M4 M5 M6 M7 Δ1 Δ32 Δ54 Δ76 Δ7654 =
      fun i j =>
        higham8_13_fanIn7Matrix n M1 M2 M3 M4 M5 M6 M7 i j +
          higham8_14_fanIn7LocalLinearMatrix
            (M7 * M6) (M5 * M4) (M3 * M2) M1
            Δ76 Δ54 Δ32 Δ1 Δ7654 i j +
          higham8_14_fanIn7LocalQuadraticRemainderMatrix
            (M7 * M6) (M5 * M4) (M3 * M2) M1
            Δ76 Δ54 Δ32 Δ1 Δ7654 i j := by
  unfold higham8_14_fanIn7RoundedMatrix higham8_13_fanIn7Matrix
  simp only [higham8_matMul_eq_matrix_mul]
  change
    (((M7 * M6 + Δ76) * (M5 * M4 + Δ54) + Δ7654) *
        ((M3 * M2 + Δ32) * (M1 + Δ1))) =
      (M7 * M6) * (M5 * M4) * ((M3 * M2) * M1) +
        higham8_14_fanIn7LocalLinearMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          Δ76 Δ54 Δ32 Δ1 Δ7654 +
        higham8_14_fanIn7LocalQuadraticRemainderMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          Δ76 Δ54 Δ32 Δ1 Δ7654
  unfold higham8_14_fanIn7LocalLinearMatrix
    higham8_14_fanIn7LocalQuadraticRemainderMatrix
  noncomm_ring

/-- Entrywise asymptotic comparison for a family of fixed-size matrices. -/
def Higham8MatrixFamilyIsBigO {ι : Type*} {n : ℕ} (l : Filter ι)
    (scale : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (fun t => X t i j) =O[l] scale

namespace Higham8MatrixFamilyIsBigO

theorem const {ι : Type*} {n : ℕ} {l : Filter ι}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) (fun _ => A) := by
  intro i j
  exact ScalarFamilyIsBigOOne.const (A i j)

theorem add {ι : Type*} {n : ℕ} {l : Filter ι} {s : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A)
    (hB : Higham8MatrixFamilyIsBigO l s B) :
    Higham8MatrixFamilyIsBigO l s (fun t => A t + B t) := by
  intro i j
  simpa using (hA i j).add (hB i j)

theorem abs {ι : Type*} {n : ℕ} {l : Filter ι} {s : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A) :
    Higham8MatrixFamilyIsBigO l s (fun t i j => |A t i j|) := by
  intro i j
  simpa only [Real.norm_eq_abs] using (hA i j).norm_left

theorem mul {ι : Type*} {n : ℕ} {l : Filter ι} {s r : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l s A)
    (hB : Higham8MatrixFamilyIsBigO l r B) :
    Higham8MatrixFamilyIsBigO l (fun t => s t * r t)
      (fun t => A t * B t) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Asymptotics.IsBigO.sum
  intro k _hk
  exact (hA i k).mul (hB k j)

theorem unit_mul_unit {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hB : Higham8MatrixFamilyIsBigO l u B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [pow_two] using hA.mul hB

theorem unit_mul_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l u (fun t => A t * B t) := by
  simpa only [mul_one] using hA.mul hB

theorem one_mul_unit {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l u B) :
    Higham8MatrixFamilyIsBigO l u (fun t => A t * B t) := by
  simpa only [one_mul] using hA.mul hB

theorem sq_mul_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [mul_one] using hA.mul hB

theorem one_mul_sq {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A B : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) B) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) (fun t => A t * B t) := by
  simpa only [one_mul] using hA.mul hB

theorem unit_to_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l u A)
    (hu : Tendsto u l (𝓝 0)) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A := by
  intro i j
  exact (hA i j).trans (hu.isBigO_one ℝ)

theorem sq_to_one {ι : Type*} {n : ℕ} {l : Filter ι} {u : ι → ℝ}
    {A : ι → Matrix (Fin n) (Fin n) ℝ}
    (hA : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) A)
    (hu : Tendsto u l (𝓝 0)) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A := by
  intro i j
  exact (hA i j).trans ((hu.pow 2).isBigO_one ℝ)

end Higham8MatrixFamilyIsBigO

/-- A rounded matrix product of two entrywise `O(1)` matrix families remains
entrywise `O(1)` when the fixed inner dimension is used and `u → 0`. -/
theorem higham8_fl_matMul_family_isBigO_one
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (hvalid : ∀ t, gammaValid (fp t) n)
    (A B : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A)
    (hB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B) :
    Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => fl_matMul (fp t) n n n (A t) (B t)) := by
  have hg := higham8_18_gamma_family_isBigO_unit fp n hu
  have hu_one : (fun t => (fp t).u) =O[l] (fun _ : ι => (1 : ℝ)) :=
    hu.isBigO_one ℝ
  let Aabs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |A t i j|
  let Babs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |B t i j|
  have hAabs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) Aabs :=
    hA.abs
  have hBabs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) Babs :=
    hB.abs
  have hprod : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => A t * B t) := by
    simpa only [one_mul] using hA.mul hB
  have habsProd : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => Aabs t * Babs t) := by
    simpa only [one_mul] using hAabs.mul hBabs
  intro i j
  let E : ι → ℝ := fun t =>
    ∑ k : Fin n, |A t i k| * |B t k j|
  have hE : E =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa only [E, Aabs, Babs, Matrix.mul_apply] using habsProd i j
  have hbudget : (fun t => gamma (fp t) n * E t) =O[l]
      (fun t => (fp t).u) := by
    simpa only [mul_one] using hg.mul hE
  have herrBudget :
      (fun t => fl_matMul (fp t) n n n (A t) (B t) i j -
        (A t * B t) i j) =O[l]
        (fun t => gamma (fp t) n * E t) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    have hγ : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvalid t)
    have hE0 : 0 ≤ E t :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have herr := matMul_error_bound (fp t) n n n (A t) (B t) (hvalid t) i j
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hγ,
      abs_of_nonneg hE0, abs_mul, E, higham8_matMul_eq_matrix_mul] using herr
  have herrOne := (herrBudget.trans hbudget).trans hu_one
  have hsum := herrOne.add (hprod i j)
  convert hsum using 1
  funext t
  ring

/-- A local perturbation bounded by `gamma_n` times a nonnegative `O(1)`
matrix envelope is entrywise `O(u)`. -/
theorem higham8_localDelta_family_isBigO_unit_of_gamma_envelope
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (hvalid : ∀ t, gammaValid (fp t) n)
    (Δ E : ι → Matrix (Fin n) (Fin n) ℝ)
    (hE : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E)
    (hE_nonneg : ∀ t i j, 0 ≤ E t i j)
    (hΔ : ∀ t i j, |Δ t i j| ≤ gamma (fp t) n * E t i j) :
    Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ := by
  have hg := higham8_18_gamma_family_isBigO_unit fp n hu
  intro i j
  have hbudget : (fun t => gamma (fp t) n * E t i j) =O[l]
      (fun t => (fp t).u) := by
    simpa only [mul_one] using hg.mul (hE i j)
  have hcompare : (fun t => Δ t i j) =O[l]
      (fun t => gamma (fp t) n * E t i j) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with t
    have hγ : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvalid t)
    simpa only [Real.norm_eq_abs, one_mul, abs_mul, abs_of_nonneg hγ,
      abs_of_nonneg (hE_nonneg t i j)] using hΔ t i j
  exact hcompare.trans hbudget

/-- The cross terms in the exact local expansion are uniformly `O(u²)` as
soon as each of the five local perturbation matrices is entrywise `O(u)`.
This is precisely the step hidden by the source's `+ O(u²)` notation. -/
theorem higham8_14_fanIn7LocalQuadraticRemainder_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} {n : ℕ} (u : ι → ℝ)
    (hu : Tendsto u l (𝓝 0))
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (a b c d e : ι → Matrix (Fin n) (Fin n) ℝ)
    (ha : Higham8MatrixFamilyIsBigO l u a)
    (hb : Higham8MatrixFamilyIsBigO l u b)
    (hc : Higham8MatrixFamilyIsBigO l u c)
    (hd : Higham8MatrixFamilyIsBigO l u d)
    (he : Higham8MatrixFamilyIsBigO l u e) :
    Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2)
      (fun t => higham8_14_fanIn7LocalQuadraticRemainderMatrix
        A B C D (a t) (b t) (c t) (d t) (e t)) := by
  let A₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => A
  let B₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => B
  let C₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => C
  let D₀ : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => D
  have hA₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) A₀ :=
    Higham8MatrixFamilyIsBigO.const A
  have hB₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) B₀ :=
    Higham8MatrixFamilyIsBigO.const B
  have hC₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C₀ :=
    Higham8MatrixFamilyIsBigO.const C
  have hD₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) D₀ :=
    Higham8MatrixFamilyIsBigO.const D
  let leftLinear : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => a t * B + A * b t + e t
  let rightLinear : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => c t * D + C * d t
  let ab : ι → Matrix (Fin n) (Fin n) ℝ := fun t => a t * b t
  let cd : ι → Matrix (Fin n) (Fin n) ℝ := fun t => c t * d t
  have hleft : Higham8MatrixFamilyIsBigO l u leftLinear := by
    exact ((ha.unit_mul_one hB₀).add (hA₀.one_mul_unit hb)).add he
  have hright : Higham8MatrixFamilyIsBigO l u rightLinear := by
    exact (hc.unit_mul_one hD₀).add (hC₀.one_mul_unit hd)
  have hab : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) ab :=
    ha.unit_mul_unit hb
  have hcd : Higham8MatrixFamilyIsBigO l (fun t => u t ^ 2) cd :=
    hc.unit_mul_unit hd
  have hCD : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => C * D) := Higham8MatrixFamilyIsBigO.const (C * D)
  have hAB : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => A * B) := Higham8MatrixFamilyIsBigO.const (A * B)
  have h1 := hab.sq_mul_one hCD
  have h2 := hAB.one_mul_sq hcd
  have h3 := hleft.unit_mul_unit hright
  have h4 := (hleft.unit_to_one hu).one_mul_sq hcd
  have h5 := hab.sq_mul_one (hright.unit_to_one hu)
  have h6 := hab.sq_mul_one (hcd.sq_to_one hu)
  have hsum := ((((h1.add h2).add h3).add h4).add h5).add h6
  simpa only [higham8_14_fanIn7LocalQuadraticRemainderMatrix,
    leftLinear, rightLinear, ab, cd, A₀, B₀, C₀, D₀] using hsum

/-- Literal-producer closure for the local expansion.  For an actual family
of fan-in executions, one can choose the five perturbation matrices in (8.14)
simultaneously so that every one is entrywise `O(u)` and the complete omitted
cross-term matrix is entrywise `O(u²)`. -/
theorem higham8_14_fanIn7Executor_has_local_O_unit_expansion
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (M1 M2 M3 M4 M5 M6 M7 : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n) :
    ∃ Δ1 Δ32 Δ54 Δ76 Δ7654 : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ t,
        higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b =
          higham8_14_fanIn7RoundedApply n
            M1 M2 M3 M4 M5 M6 M7
            (Δ1 t) (Δ32 t) (Δ54 t) (Δ76 t) (Δ7654 t) b) ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ1 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ32 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ54 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ76 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ7654 ∧
      Higham8MatrixFamilyIsBigO l (fun t => (fp t).u ^ 2)
        (fun t => higham8_14_fanIn7LocalQuadraticRemainderMatrix
          (M7 * M6) (M5 * M4) (M3 * M2) M1
          (Δ76 t) (Δ54 t) (Δ32 t) (Δ1 t) (Δ7654 t)) := by
  classical
  have hp := fun t => higham8_14_fanIn7Executor_eq_roundedApply
    (fp t) n M1 M2 M3 M4 M5 M6 M7 b (hvalid t)
  choose Δ1 Δ32 Δ54 Δ76 Δ7654 hrest using hp
  let C32 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M3 M2
  let C54 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M5 M4
  let C76 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n M7 M6
  let C7654 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fl_matMul (fp t) n n n (C76 t) (C54 t)
  have hC32 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C32 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M3) (fun _ => M2)
      (Higham8MatrixFamilyIsBigO.const M3)
      (Higham8MatrixFamilyIsBigO.const M2)
  have hC54 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C54 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M5) (fun _ => M4)
      (Higham8MatrixFamilyIsBigO.const M5)
      (Higham8MatrixFamilyIsBigO.const M4)
  have hC76 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C76 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid
      (fun _ => M7) (fun _ => M6)
      (Higham8MatrixFamilyIsBigO.const M7)
      (Higham8MatrixFamilyIsBigO.const M6)
  have hC7654 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C7654 := by
    exact higham8_fl_matMul_family_isBigO_one fp hu n hvalid C76 C54 hC76 hC54
  let E1₀ : Matrix (Fin n) (Fin n) ℝ := fun i j => |M1 i j|
  let E1 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E1₀
  have hE1 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E1 :=
    Higham8MatrixFamilyIsBigO.const E1₀
  have hΔ1 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ1 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ1 E1 hE1
    · intro t i j
      exact abs_nonneg (M1 i j)
    · intro t i j
      simpa only [E1, E1₀] using (hrest t).2.1 i j
  let E54₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M5 i k| * |M4 k j|
  let E54 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E54₀
  have hE54 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E54 :=
    Higham8MatrixFamilyIsBigO.const E54₀
  have hΔ54 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ54 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ54 E54 hE54
    · intro t i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · intro t i j
      simpa only [E54, E54₀] using (hrest t).2.2.2.1 i j
  let E76₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M7 i k| * |M6 k j|
  let E76 : ι → Matrix (Fin n) (Fin n) ℝ := fun _ => E76₀
  have hE76 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E76 :=
    Higham8MatrixFamilyIsBigO.const E76₀
  have hΔ76 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ76 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ76 E76 hE76
    · intro t i j
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · intro t i j
      simpa only [E76, E76₀] using (hrest t).2.2.2.2.1 i j
  let E32₀ : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => ∑ k : Fin n, |M3 i k| * |M2 k j|
  let C32abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C32 t i j|
  let E32 : ι → Matrix (Fin n) (Fin n) ℝ := fun t => E32₀ + C32abs t
  have hE32₀ : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun _ => E32₀) := Higham8MatrixFamilyIsBigO.const E32₀
  have hC32abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C32abs :=
    hC32.abs
  have hE32 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E32 :=
    hE32₀.add hC32abs
  have hΔ32 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ32 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ32 E32 hE32
    · intro t i j
      exact add_nonneg
        (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        (abs_nonneg (C32 t i j))
    · intro t i j
      calc
        |Δ32 t i j| ≤
            gamma (fp t) n * E32₀ i j + gamma (fp t) n * |C32 t i j| := by
          simpa only [E32₀, C32] using (hrest t).2.2.1 i j
        _ = gamma (fp t) n * E32 t i j := by
          simp only [E32, C32abs, Matrix.add_apply]
          ring
  let C54abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C54 t i j|
  let C76abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C76 t i j|
  let C7654abs : ι → Matrix (Fin n) (Fin n) ℝ := fun t i j => |C7654 t i j|
  let E7654 : ι → Matrix (Fin n) (Fin n) ℝ :=
    fun t => C76abs t * C54abs t + C7654abs t
  have hC54abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C54abs :=
    hC54.abs
  have hC76abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C76abs :=
    hC76.abs
  have hC7654abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) C7654abs :=
    hC7654.abs
  have hC76C54abs : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ))
      (fun t => C76abs t * C54abs t) := by
    simpa only [one_mul] using hC76abs.mul hC54abs
  have hE7654 : Higham8MatrixFamilyIsBigO l (fun _ : ι => (1 : ℝ)) E7654 :=
    hC76C54abs.add hC7654abs
  have hΔ7654 : Higham8MatrixFamilyIsBigO l (fun t => (fp t).u) Δ7654 := by
    apply higham8_localDelta_family_isBigO_unit_of_gamma_envelope
      fp hu n hvalid Δ7654 E7654 hE7654
    · intro t i j
      have hprod : 0 ≤ (C76abs t * C54abs t) i j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact add_nonneg hprod (abs_nonneg (C7654 t i j))
    · intro t i j
      calc
        |Δ7654 t i j| ≤
            gamma (fp t) n *
                (∑ k : Fin n, |C76 t i k| * |C54 t k j|) +
              gamma (fp t) n * |C7654 t i j| := by
          simpa only [C76, C54, C7654] using (hrest t).2.2.2.2.2 i j
        _ = gamma (fp t) n * E7654 t i j := by
          simp only [E7654, C76abs, C54abs, C7654abs,
            Matrix.add_apply, Matrix.mul_apply]
          ring
  have hquadratic :=
    higham8_14_fanIn7LocalQuadraticRemainder_isBigO_unit_sq
      (fun t => (fp t).u) hu (M7 * M6) (M5 * M4) (M3 * M2) M1
      Δ76 Δ54 Δ32 Δ1 Δ7654 hΔ76 hΔ54 hΔ32 hΔ1 hΔ7654
  exact ⟨Δ1, Δ32, Δ54, Δ76, Δ7654,
    fun t => (hrest t).1, hΔ1, hΔ32, hΔ54, hΔ76, hΔ7654, hquadratic⟩

/-! ## Chapter 9, Theorem 9.15: Barrlund's normwise endpoint -/

/-- Higham, Theorem 9.15 / equation (9.27), with the audited target-critical
`min` premise discharged by Barrlund's two resolvent arguments.

The extra inverse witnesses are structural: they certify the inverses of the
two perturbed triangular factors used in the two mirrored resolvent proofs.
No estimate on either unknown factor perturbation is assumed. -/
theorem higham9_15_barrlund_normwise_factor_bounds_without_min_premise
    {n : ℕ}
    (A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv :
      Matrix (Fin n) (Fin n) ℝ)
    (hLU : L * U = A)
    (hPert : (L + ΔL) * (U + ΔU) = A + ΔA)
    (hΔL_strict : ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper : ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hLinv_lower : ∀ i j : Fin n, i.val < j.val → Linv i j = 0)
    (hUinv_upper : ∀ i j : Fin n, j.val < i.val → Uinv i j = 0)
    (hLΔLinv_lower : ∀ i j : Fin n, i.val < j.val → LΔLinv i j = 0)
    (hUΔUinv_upper : ∀ i j : Fin n, j.val < i.val → UΔUinv i j = 0)
    (hLinvL : Linv * L = 1)
    (hLLinv : L * Linv = 1)
    (hUinvU : Uinv * U = 1)
    (hUΔUinvR : (U + ΔU) * UΔUinv = 1)
    (hLΔLinvL : LΔLinv * (L + ΔL) = 1)
    (hGlt : opNorm2 (Linv * ΔA * Uinv) < 1) :
    frobNormRect ΔL ≤
        opNorm2 L * frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) ∧
      frobNormRect ΔU ≤
        frobNormRect (Linv * ΔA * Uinv) * opNorm2 U /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
  let G : Matrix (Fin n) (Fin n) ℝ := Linv * ΔA * Uinv
  have hLrect : rectOpNorm2Le L (opNorm2 L) :=
    opNorm2Le_to_rectOpNorm2Le (opNorm2Le_opNorm2 L)
  have hGrect : rectOpNorm2Le G (opNorm2 G) :=
    opNorm2Le_to_rectOpNorm2Le (opNorm2Le_opNorm2 G)
  have hUt : opNorm2Le (matTranspose U) (opNorm2 U) :=
    opNorm2Le_transpose U (opNorm2_nonneg U) (opNorm2Le_opNorm2 U)
  have hUrect : rectOpNorm2Le (finiteTranspose U) (opNorm2 U) := by
    simpa [finiteTranspose, matTranspose] using
      opNorm2Le_to_rectOpNorm2Le hUt
  have hGt : opNorm2Le (matTranspose G) (opNorm2 G) :=
    opNorm2Le_transpose G (opNorm2_nonneg G) (opNorm2Le_opNorm2 G)
  have hGrectT : rectOpNorm2Le (finiteTranspose G) (opNorm2 G) := by
    simpa [finiteTranspose, matTranspose] using
      opNorm2Le_to_rectOpNorm2Le hGt
  constructor
  · simpa [G] using
      higham9_15_barrlund_deltaL_bound
        A L U ΔA ΔL ΔU Linv Uinv UΔUinv hLU hPert
        hΔL_strict hΔU_upper hLinv_lower hUΔUinv_upper
        hLinvL hLLinv hUinvU hUΔUinvR
        (opNorm2_nonneg L) (opNorm2_nonneg G) (by simpa [G] using hGlt)
        hLrect hGrect
  · simpa [G] using
      higham9_15_barrlund_deltaU_bound
        A L U ΔA ΔL ΔU Linv Uinv LΔLinv hLU hPert
        hΔL_strict hΔU_upper hUinv_upper hLΔLinv_lower
        hLLinv hUinvU hLΔLinvL
        (opNorm2_nonneg U) (opNorm2_nonneg G) (by simpa [G] using hGlt)
        hUrect hGrectT

/-- Source-normalized form of the preceding theorem.  This is the printed
Theorem 9.15 maximum-ratio conclusion with `‖G‖₂` and `‖G‖F`, and it contains
no hypothesis equivalent to the missing conclusion. -/
theorem higham9_15_barrlund_normwise_source_ratio_without_min_premise
    {n : ℕ} [Nonempty (Fin n)]
    (A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv :
      Matrix (Fin n) (Fin n) ℝ)
    (hLU : L * U = A)
    (hPert : (L + ΔL) * (U + ΔU) = A + ΔA)
    (hΔL_strict : ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper : ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hLinv_lower : ∀ i j : Fin n, i.val < j.val → Linv i j = 0)
    (hUinv_upper : ∀ i j : Fin n, j.val < i.val → Uinv i j = 0)
    (hLΔLinv_lower : ∀ i j : Fin n, i.val < j.val → LΔLinv i j = 0)
    (hUΔUinv_upper : ∀ i j : Fin n, j.val < i.val → UΔUinv i j = 0)
    (hLinvL : Linv * L = 1)
    (hLLinv : L * Linv = 1)
    (hUinvU : Uinv * U = 1)
    (hUΔUinvR : (U + ΔU) * UΔUinv = 1)
    (hLΔLinvL : LΔLinv * (L + ΔL) = 1)
    (hGlt : opNorm2 (Linv * ΔA * Uinv) < 1) :
    max (frobNormRect ΔL / opNorm2 L)
        (frobNormRect ΔU / opNorm2 U) ≤
      frobNormRect (Linv * ΔA * Uinv) /
        (1 - opNorm2 (Linv * ΔA * Uinv)) := by
  have hb :=
    higham9_15_barrlund_normwise_factor_bounds_without_min_premise
      A L U ΔA ΔL ΔU Linv Uinv LΔLinv UΔUinv hLU hPert
      hΔL_strict hΔU_upper hLinv_lower hUinv_upper
      hLΔLinv_lower hUΔUinv_upper hLinvL hLLinv hUinvU
      hUΔUinvR hLΔLinvL hGlt
  have hLrect : rectMatMul L Linv = idMatrix n := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hLLinv
    simpa [rectMatMul, Matrix.mul_apply, idMatrix] using hij
  have hUrect : rectMatMul Uinv U = idMatrix n := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hUinvU
    simpa [rectMatMul, Matrix.mul_apply, idMatrix] using hij
  have hLpos : 0 < opNorm2 L :=
    higham9_15_opNorm2_pos_of_rectMatMul_right_inverse L Linv hLrect
  have hUpos : 0 < opNorm2 U :=
    higham9_15_opNorm2_pos_of_rectMatMul_left_inverse U Uinv hUrect
  apply max_le
  · calc
      frobNormRect ΔL / opNorm2 L ≤
          (opNorm2 L * frobNormRect (Linv * ΔA * Uinv) /
            (1 - opNorm2 (Linv * ΔA * Uinv))) / opNorm2 L :=
        div_le_div_of_nonneg_right hb.1 (le_of_lt hLpos)
      _ = frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
        field_simp [ne_of_gt hLpos]
  · calc
      frobNormRect ΔU / opNorm2 U ≤
          (frobNormRect (Linv * ΔA * Uinv) * opNorm2 U /
            (1 - opNorm2 (Linv * ΔA * Uinv))) / opNorm2 U :=
        div_le_div_of_nonneg_right hb.2 (le_of_lt hUpos)
      _ = frobNormRect (Linv * ΔA * Uinv) /
          (1 - opNorm2 (Linv * ΔA * Uinv)) := by
        field_simp [ne_of_gt hUpos]

/-! ## Chapter 9, Theorem 9.15: Sun's componentwise mixed-resolvent endpoint -/

/-- Right-handed form of the nonnegative resolvent comparison. -/
theorem higham9_15_resolvent_matrix_majorant_right_of_componentwise_inequality
    {n : ℕ} (M R V W : Matrix (Fin n) (Fin n) ℝ)
    (hR : ch7NonnegativeResolvent n M R)
    (hineq : ∀ i j : Fin n,
      W i j ≤ V i j + rectMatMul W M i j) :
    ∀ i j : Fin n, W i j ≤ rectMatMul V R i j := by
  have hRT : ch7NonnegativeResolvent n
      (finiteTranspose M) (finiteTranspose R) := by
    refine ⟨?_, ?_⟩
    · intro i j
      exact hR.1 j i
    · have hright : IsRightInverse n (matSub_id n M) R :=
        ch7_isRightInverse_of_isLeftInverse hR.2
      have ht := isLeftInverse_finiteTranspose_of_isRightInverse hright
      have hsubT : finiteTranspose (matSub_id n M) =
          matSub_id n (finiteTranspose M) := by
        ext i j
        simp [finiteTranspose, matSub_id, idMatrix, eq_comm]
      simpa [hsubT] using ht
  have hineqT : ∀ i j : Fin n,
      finiteTranspose W i j ≤
        finiteTranspose V i j +
          rectMatMul (finiteTranspose M) (finiteTranspose W) i j := by
    intro i j
    have h := hineq j i
    simpa [finiteTranspose, rectMatMul, mul_comm] using h
  have hmajorT :=
    higham9_15_resolvent_matrix_majorant_of_componentwise_inequality
      (finiteTranspose M) (finiteTranspose R)
      (finiteTranspose V) (finiteTranspose W) hRT hineqT
  intro i j
  have h := hmajorT j i
  simpa [finiteTranspose, rectMatMul, mul_comm] using h

/-- Sun's mixed-inverse comparison kernel. The two mixed residuals satisfy
genuine one-sided resolvent inequalities, so this proof does not use the
unavailable nonlinear self-majorant route. -/
theorem higham9_15_sun_mixed_resolvent_normalized_bounds
    {n : ℕ}
    (G X Y P Q Z T R : Matrix (Fin n) (Fin n) ℝ)
    (hZsplit : Z = X + Q)
    (hZres : Z = G + G * Q)
    (hTsplit : T = P + Y)
    (hTres : T = G + P * G)
    (hX : ∀ i j : Fin n, i.val ≤ j.val → X i j = 0)
    (hY : ∀ i j : Fin n, j.val < i.val → Y i j = 0)
    (hP : ∀ i j : Fin n, i.val ≤ j.val → P i j = 0)
    (hQ : ∀ i j : Fin n, j.val < i.val → Q i j = 0)
    (hR : ch7NonnegativeResolvent n (absMatrix n G) R) :
    (∀ i j : Fin n,
      |X i j| ≤
        higham9_15_strilPart
          (rectMatMul R (absMatrix n G)) i j) ∧
      (∀ i j : Fin n,
        |Y i j| ≤
          higham9_15_triuPart
            (rectMatMul (absMatrix n G) R) i j) := by
  let C : Matrix (Fin n) (Fin n) ℝ := absMatrix n G
  let WZ : Matrix (Fin n) (Fin n) ℝ := absMatrix n Z
  let WT : Matrix (Fin n) (Fin n) ℝ := absMatrix n T
  have hstrilZ : higham9_15_strilPart Z = X := by
    rw [hZsplit]
    exact higham9_15_strilPart_add_strictLower_upper X Q hX hQ
  have htriuZ : higham9_15_triuPart Z = Q := by
    rw [hZsplit]
    exact higham9_15_triuPart_add_strictLower_upper X Q hX hQ
  have hstrilT : higham9_15_strilPart T = P := by
    rw [hTsplit]
    exact higham9_15_strilPart_add_strictLower_upper P Y hP hY
  have htriuT : higham9_15_triuPart T = Y := by
    rw [hTsplit]
    exact higham9_15_triuPart_add_strictLower_upper P Y hP hY
  have hQabs : ∀ i j : Fin n, |Q i j| ≤ |Z i j| := by
    intro i j
    rw [← htriuZ]
    unfold higham9_15_triuPart
    by_cases hij : i.val ≤ j.val
    · simp [hij]
    · simp [hij, abs_nonneg]
  have hPabs : ∀ i j : Fin n, |P i j| ≤ |T i j| := by
    intro i j
    rw [← hstrilT]
    unfold higham9_15_strilPart
    by_cases hji : j.val < i.val
    · simp [hji]
    · simp [hji, abs_nonneg]
  have hZineq : ∀ i j : Fin n,
      WZ i j ≤ C i j + rectMatMul C WZ i j := by
    intro i j
    calc
      WZ i j = |G i j + (G * Q) i j| := by
        simp only [WZ, absMatrix]
        rw [hZres]
        rfl
      _ ≤ |G i j| + |(G * Q) i j| := abs_add_le _ _
      _ ≤ |G i j| +
          rectMatMul (absMatrix n G) (absMatrix n Q) i j :=
        add_le_add_right
          (higham9_15_abs_matrix_mul_le_abs_mul_abs G Q i j) _
      _ ≤ C i j + rectMatMul C WZ i j := by
        simp only [C, WZ, absMatrix, rectMatMul]
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hQabs k j) (abs_nonneg (G i k))
  have hTineq : ∀ i j : Fin n,
      WT i j ≤ C i j + rectMatMul WT C i j := by
    intro i j
    calc
      WT i j = |G i j + (P * G) i j| := by
        simp only [WT, absMatrix]
        rw [hTres]
        rfl
      _ ≤ |G i j| + |(P * G) i j| := abs_add_le _ _
      _ ≤ |G i j| +
          rectMatMul (absMatrix n P) (absMatrix n G) i j :=
        add_le_add_right
          (higham9_15_abs_matrix_mul_le_abs_mul_abs P G i j) _
      _ ≤ C i j + rectMatMul WT C i j := by
        simp only [C, WT, absMatrix, rectMatMul]
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hPabs i k) (abs_nonneg (G k j))
  have hZmajor : ∀ i j : Fin n,
      WZ i j ≤ rectMatMul R C i j :=
    higham9_15_resolvent_matrix_majorant_of_componentwise_inequality
      C R C WZ (by simpa [C] using hR) hZineq
  have hTmajor : ∀ i j : Fin n,
      WT i j ≤ rectMatMul C R i j :=
    higham9_15_resolvent_matrix_majorant_right_of_componentwise_inequality
      C R C WT (by simpa [C] using hR) hTineq
  have hRCnonneg : ∀ i j : Fin n,
      0 ≤ rectMatMul R C i j := by
    intro i j
    unfold rectMatMul C
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hR.1 i k) (abs_nonneg (G k j))
  have hCRnonneg : ∀ i j : Fin n,
      0 ≤ rectMatMul C R i j := by
    intro i j
    unfold rectMatMul C
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg (G i k)) (hR.1 k j)
  constructor
  · intro i j
    calc
      |X i j| = |higham9_15_strilPart Z i j| := by rw [hstrilZ]
      _ ≤ higham9_15_strilPart (rectMatMul R C) i j :=
        higham9_15_abs_strilPart_le_strilPart_of_abs_le
          Z (rectMatMul R C) hRCnonneg
          (by
            intro r c
            simpa [WZ] using hZmajor r c) i j
      _ = higham9_15_strilPart
          (rectMatMul R (absMatrix n G)) i j := by rfl
  · intro i j
    calc
      |Y i j| = |higham9_15_triuPart T i j| := by rw [htriuT]
      _ ≤ higham9_15_triuPart (rectMatMul C R) i j :=
        higham9_15_abs_triuPart_le_triuPart_of_abs_le
          T (rectMatMul C R) hCRnonneg
          (by
            intro r c
            simpa [WT] using hTmajor r c) i j
      _ = higham9_15_triuPart
          (rectMatMul (absMatrix n G) R) i j := by rfl

/-- Source-factor form of Sun's mixed-inverse argument. The additional
inverse witnesses belong to the unperturbed factors `Lhat - ΔL` and
`Uhat - ΔU`; they are structural and do not encode either bound. -/
theorem higham9_15_sun_componentwise_source_bounds_of_resolvent
    {n : ℕ}
    (A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU R :
      Matrix (Fin n) (Fin n) ℝ)
    (hA : (Lhat - ΔL) * (Uhat - ΔU) = A)
    (hPert : Lhat * Uhat = A + ΔA)
    (hLhatLeft : LhatInv * Lhat = 1)
    (hLhatRight : Lhat * LhatInv = 1)
    (hUhatRight : Uhat * UhatInv = 1)
    (hUhatLeft : UhatInv * Uhat = 1)
    (hLbaseLeft : LbaseInv * (Lhat - ΔL) = 1)
    (hUbaseRight : (Uhat - ΔU) * UbaseInv = 1)
    (hLhatInv_lower :
      ∀ i j : Fin n, i.val < j.val → LhatInv i j = 0)
    (hUhatInv_upper :
      ∀ i j : Fin n, j.val < i.val → UhatInv i j = 0)
    (hLbaseInv_lower :
      ∀ i j : Fin n, i.val < j.val → LbaseInv i j = 0)
    (hUbaseInv_upper :
      ∀ i j : Fin n, j.val < i.val → UbaseInv i j = 0)
    (hΔL_strict :
      ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper :
      ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hR : ch7NonnegativeResolvent n
      (absMatrix n (higham9_27_GMatrix LhatInv ΔA UhatInv)) R) :
    (∀ i j : Fin n, |ΔL i j| ≤
        rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)) R))
          (absMatrix n Uhat) i j) := by
  let G : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔA * UhatInv
  let X : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔL
  let Y : Matrix (Fin n) (Fin n) ℝ := ΔU * UhatInv
  let P : Matrix (Fin n) (Fin n) ℝ := LbaseInv * ΔL
  let Q : Matrix (Fin n) (Fin n) ℝ := ΔU * UbaseInv
  let Z : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔA * UbaseInv
  let T : Matrix (Fin n) (Fin n) ℝ := LbaseInv * ΔA * UhatInv
  have hΔA_lower :
      ΔA = Lhat * ΔU + ΔL * (Uhat - ΔU) := by
    calc
      ΔA = (A + ΔA) - A := by abel
      _ = Lhat * Uhat - (Lhat - ΔL) * (Uhat - ΔU) := by
        rw [hPert, hA]
      _ = Lhat * ΔU + ΔL * (Uhat - ΔU) := by noncomm_ring
  have hΔA_upper :
      ΔA = (Lhat - ΔL) * ΔU + ΔL * Uhat := by
    calc
      ΔA = (A + ΔA) - A := by abel
      _ = Lhat * Uhat - (Lhat - ΔL) * (Uhat - ΔU) := by
        rw [hPert, hA]
      _ = (Lhat - ΔL) * ΔU + ΔL * Uhat := by noncomm_ring
  have hZsplit : Z = X + Q := by
    dsimp [Z, X, Q]
    rw [hΔA_lower]
    calc
      LhatInv * (Lhat * ΔU + ΔL * (Uhat - ΔU)) * UbaseInv =
          (LhatInv * Lhat) * ΔU * UbaseInv +
            LhatInv * ΔL * ((Uhat - ΔU) * UbaseInv) := by
        noncomm_ring
      _ = LhatInv * ΔL + ΔU * UbaseInv := by
        rw [hLhatLeft, hUbaseRight]
        noncomm_ring
  have hZres : Z = G + G * Q := by
    dsimp [Z, G, Q]
    calc
      LhatInv * ΔA * UbaseInv =
          (LhatInv * ΔA * UhatInv) * Uhat * UbaseInv := by
        symm
        calc
          (LhatInv * ΔA * UhatInv) * Uhat * UbaseInv =
              LhatInv * ΔA * (UhatInv * Uhat) * UbaseInv := by
            simp only [mul_assoc]
          _ = LhatInv * ΔA * UbaseInv := by
            rw [hUhatLeft]
            simp
      _ = (LhatInv * ΔA * UhatInv) *
          (((Uhat - ΔU) * UbaseInv) + ΔU * UbaseInv) := by
        noncomm_ring
      _ = LhatInv * ΔA * UhatInv +
          (LhatInv * ΔA * UhatInv) * (ΔU * UbaseInv) := by
        rw [hUbaseRight]
        noncomm_ring
  have hTsplit : T = P + Y := by
    dsimp [T, P, Y]
    rw [hΔA_upper]
    calc
      LbaseInv * ((Lhat - ΔL) * ΔU + ΔL * Uhat) * UhatInv =
          (LbaseInv * (Lhat - ΔL)) * ΔU * UhatInv +
            LbaseInv * ΔL * (Uhat * UhatInv) := by
        noncomm_ring
      _ = LbaseInv * ΔL + ΔU * UhatInv := by
        rw [hLbaseLeft, hUhatRight]
        noncomm_ring
  have hTres : T = G + P * G := by
    dsimp [T, G, P]
    calc
      LbaseInv * ΔA * UhatInv =
          LbaseInv * Lhat * (LhatInv * ΔA * UhatInv) := by
        symm
        calc
          LbaseInv * Lhat * (LhatInv * ΔA * UhatInv) =
              LbaseInv * (Lhat * LhatInv) * ΔA * UhatInv := by
            simp only [mul_assoc]
          _ = LbaseInv * ΔA * UhatInv := by
            rw [hLhatRight]
            simp
      _ = ((LbaseInv * (Lhat - ΔL)) + LbaseInv * ΔL) *
          (LhatInv * ΔA * UhatInv) := by
        noncomm_ring
      _ = LhatInv * ΔA * UhatInv +
          (LbaseInv * ΔL) * (LhatInv * ΔA * UhatInv) := by
        rw [hLbaseLeft]
        noncomm_ring
  have hX : ∀ i j : Fin n, i.val ≤ j.val → X i j = 0 := by
    simpa [X, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_lower_strictLower_is_strictLower
        LhatInv ΔL hLhatInv_lower hΔL_strict
  have hY : ∀ i j : Fin n, j.val < i.val → Y i j = 0 := by
    simpa [Y, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_upper_upper_is_upper
        ΔU UhatInv hΔU_upper hUhatInv_upper
  have hP : ∀ i j : Fin n, i.val ≤ j.val → P i j = 0 := by
    simpa [P, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_lower_strictLower_is_strictLower
        LbaseInv ΔL hLbaseInv_lower hΔL_strict
  have hQ : ∀ i j : Fin n, j.val < i.val → Q i j = 0 := by
    simpa [Q, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_upper_upper_is_upper
        ΔU UbaseInv hΔU_upper hUbaseInv_upper
  have hGsource :
      G = higham9_27_GMatrix LhatInv ΔA UhatInv := by
    ext i j
    simp [G, higham9_27_GMatrix, rectMatMul, Matrix.mul_apply]
  have hnorm :=
    higham9_15_sun_mixed_resolvent_normalized_bounds
      G X Y P Q Z T R hZsplit hZres hTsplit hTres hX hY hP hQ
      (by simpa [hGsource] using hR)
  constructor
  · intro i j
    have hΔLeq : ΔL = Lhat * X := by
      dsimp [X]
      calc
        ΔL = 1 * ΔL := by simp
        _ = (Lhat * LhatInv) * ΔL := by rw [hLhatRight]
        _ = Lhat * (LhatInv * ΔL) := by rw [mul_assoc]
    calc
      |ΔL i j| = |(Lhat * X) i j| := by rw [hΔLeq]
      _ ≤ rectMatMul (absMatrix n Lhat) (absMatrix n X) i j :=
        higham9_15_abs_matrix_mul_le_abs_mul_abs Lhat X i j
      _ ≤ rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R (absMatrix n G))) i j := by
        unfold rectMatMul absMatrix
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hnorm.1 k j) (abs_nonneg (Lhat i k))
      _ = rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j := by
        rw [hGsource]
  · intro i j
    have hΔUeq : ΔU = Y * Uhat := by
      dsimp [Y]
      calc
        ΔU = ΔU * 1 := by simp
        _ = ΔU * (UhatInv * Uhat) := by rw [hUhatLeft]
        _ = (ΔU * UhatInv) * Uhat := by rw [mul_assoc]
    calc
      |ΔU i j| = |(Y * Uhat) i j| := by rw [hΔUeq]
      _ ≤ rectMatMul (absMatrix n Y) (absMatrix n Uhat) i j :=
        higham9_15_abs_matrix_mul_le_abs_mul_abs Y Uhat i j
      _ ≤ rectMatMul
          (higham9_15_triuPart
            (rectMatMul (absMatrix n G) R))
          (absMatrix n Uhat) i j := by
        unfold rectMatMul absMatrix
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hnorm.2 i k) (abs_nonneg (Uhat k j))
      _ = rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)) R))
          (absMatrix n Uhat) i j := by
        rw [hGsource]

/-- Higham Theorem 9.15's printed componentwise endpoint, with Sun's two
mixed-inverse comparisons replacing the previously assumed nonlinear
self-majorant. -/
theorem higham9_15_sun_componentwise_source_bounds_of_spectralRadius_lt_one
    {n : ℕ} (hn : 0 < n)
    (A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU :
      Matrix (Fin n) (Fin n) ℝ)
    (hA : (Lhat - ΔL) * (Uhat - ΔU) = A)
    (hPert : Lhat * Uhat = A + ΔA)
    (hLhatLeft : LhatInv * Lhat = 1)
    (hLhatRight : Lhat * LhatInv = 1)
    (hUhatRight : Uhat * UhatInv = 1)
    (hUhatLeft : UhatInv * Uhat = 1)
    (hLbaseLeft : LbaseInv * (Lhat - ΔL) = 1)
    (hUbaseRight : (Uhat - ΔU) * UbaseInv = 1)
    (hLhatInv_lower :
      ∀ i j : Fin n, i.val < j.val → LhatInv i j = 0)
    (hUhatInv_upper :
      ∀ i j : Fin n, j.val < i.val → UhatInv i j = 0)
    (hLbaseInv_lower :
      ∀ i j : Fin n, i.val < j.val → LbaseInv i j = 0)
    (hUbaseInv_upper :
      ∀ i j : Fin n, j.val < i.val → UbaseInv i j = 0)
    (hΔL_strict :
      ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper :
      ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hrho :
      spectralRadius ℂ
          (Matrix.toLin'
            (show Matrix (Fin n) (Fin n) ℂ from
              realRectToCMatrix
                (absMatrix n
                  (higham9_27_GMatrix LhatInv ΔA UhatInv)))) < 1) :
    (∀ i j : Fin n, |ΔL i j| ≤
        rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul
              (nonsingInv n
                (matSub_id n
                  (absMatrix n
                    (higham9_27_GMatrix LhatInv ΔA UhatInv))))
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv))
              (nonsingInv n
                (matSub_id n
                  (absMatrix n
                    (higham9_27_GMatrix LhatInv ΔA UhatInv))))))
          (absMatrix n Uhat) i j) := by
  let Gabs : Matrix (Fin n) (Fin n) ℝ :=
    absMatrix n (higham9_27_GMatrix LhatInv ΔA UhatInv)
  let R : Matrix (Fin n) (Fin n) ℝ :=
    nonsingInv n (matSub_id n Gabs)
  have hGabs_nonneg : ∀ i j : Fin n, 0 ≤ Gabs i j := by
    intro i j
    simp [Gabs, absMatrix]
  have hR : ch7NonnegativeResolvent n Gabs R := by
    exact
      higham9_15_nonnegative_resolvent_nonsingInv_of_spectralRadius_lt_one
        hn Gabs hGabs_nonneg (by simpa [Gabs] using hrho)
  simpa [Gabs, R] using
    higham9_15_sun_componentwise_source_bounds_of_resolvent
      A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU R
      hA hPert hLhatLeft hLhatRight hUhatRight hUhatLeft
      hLbaseLeft hUbaseRight hLhatInv_lower hUhatInv_upper
      hLbaseInv_lower hUbaseInv_upper hΔL_strict hΔU_upper
      (by simpa [Gabs] using hR)

end NumStability
