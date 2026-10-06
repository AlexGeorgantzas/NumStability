import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section01

/-!
# Higham Chapter 9: Section02

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 2.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Equation (9.2a)**, source row-permuted matrix `PA` represented by the
permutation map `sigma`.  The entry `(i,j)` is `A (sigma i) j`. -/
def higham9_2_rowPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => A (sigma i) j

/-- **Theorem 9.7 / partial-pivoting growth support**, the first row swap that
moves the selected partial-pivot row into leading position.  This is the
source row-permutation step preceding the first Schur-complement update. -/
def higham9_7_firstPivotRowSwap {m : ℕ} (r : Fin (m + 1)) :
    Fin (m + 1) → Fin (m + 1) :=
  fun i => if i = 0 then r else if i = r then 0 else i

/-- **Theorem 9.7 / partial-pivoting growth support**, the first-pivot row
swap is its own inverse. -/
theorem higham9_7_firstPivotRowSwap_involutive {m : ℕ}
    (r : Fin (m + 1)) :
    Function.Involutive (higham9_7_firstPivotRowSwap r) := by
  intro i
  unfold higham9_7_firstPivotRowSwap
  by_cases hi0 : i = 0
  · subst i
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp [hr0]
  · by_cases hir : i = r
    · subst i
      simp [hi0]
    · simp [hi0, hir]

/-- **Theorem 9.7 / partial-pivoting growth support**, the first-pivot row
swap is a permutation of the active row type. -/
theorem higham9_7_firstPivotRowSwap_isPermutation {m : ℕ}
    (r : Fin (m + 1)) :
    Function.Bijective (higham9_7_firstPivotRowSwap r) := by
  constructor
  · intro x y hxy
    have h := congrArg (higham9_7_firstPivotRowSwap r) hxy
    simpa [higham9_7_firstPivotRowSwap_involutive r x,
      higham9_7_firstPivotRowSwap_involutive r y] using h
  · intro y
    exact ⟨higham9_7_firstPivotRowSwap r y,
      higham9_7_firstPivotRowSwap_involutive r y⟩

/-- **Theorem 9.7 / partial-pivoting growth support**, permuting the rows by
the first-pivot row swap preserves nonsingularity. -/
theorem higham9_7_firstPivotRowSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective (higham9_7_firstPivotRowSwap r)
      (higham9_7_firstPivotRowSwap_isPermutation r)
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    simpa [e, higham9_2_rowPermutedMatrix, Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Theorem 9.7 / partial-pivoting growth support**, entrywise first-step
doubling bound.  After moving a partial-pivoting maximum into the leading row,
every entry of the first Schur complement is bounded by twice the original
max-entry norm.  This is the local one-step inequality behind the source
`rho_n^p <= 2^(n-1)` growth argument; it does not construct the full recursive
partial-pivoting trace. -/
theorem higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hchoice : higham9_1_partialPivotChoice A 0 r)
    (hpivot : A r 0 ≠ 0) (i j : Fin m) :
    |luFirstSchurComplement
        (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) i j| ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let sigma := higham9_7_firstPivotRowSwap r
  let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ := higham9_2_rowPermutedMatrix A sigma
  have hentry : |Aperm i.succ j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    exact entry_le_maxEntryNorm (Nat.succ_pos m) A (sigma i.succ) j.succ
  have hpivot_row : |Aperm 0 j.succ| ≤ maxEntryNorm (Nat.succ_pos m) A := by
    simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap] using
      (entry_le_maxEntryNorm (Nat.succ_pos m) A r j.succ)
  have hratio : |Aperm i.succ 0 / Aperm 0 0| ≤ 1 := by
    have hraw :=
      higham9_1_partialPivot_multiplier_abs_le_one A 0 r (sigma i.succ)
        hchoice hpivot (Nat.zero_le _)
    simpa [Aperm, higham9_2_rowPermutedMatrix, sigma, higham9_7_firstPivotRowSwap] using hraw
  have hterm :
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| ≤
        maxEntryNorm (Nat.succ_pos m) A := by
    calc
      |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
          = |Aperm i.succ 0 / Aperm 0 0| * |Aperm 0 j.succ| := by
            rw [abs_div, abs_mul, abs_div]
            ring
      _ ≤ 1 * |Aperm 0 j.succ| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * maxEntryNorm (Nat.succ_pos m) A :=
            mul_le_mul_of_nonneg_left hpivot_row zero_le_one
      _ = maxEntryNorm (Nat.succ_pos m) A := by ring
  unfold luFirstSchurComplement
  calc
    |Aperm i.succ j.succ - Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0|
        ≤ |Aperm i.succ j.succ| +
            |Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (Aperm i.succ j.succ)
              (-(Aperm i.succ 0 * Aperm 0 j.succ / Aperm 0 0))
    _ ≤ maxEntryNorm (Nat.succ_pos m) A + maxEntryNorm (Nat.succ_pos m) A :=
        add_le_add hentry hterm
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by ring

/-- **Theorem 9.7 / partial-pivoting growth support**, max-entry first-step
doubling bound for the Schur complement after the first partial-pivoting row
swap. -/
theorem higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m) (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1))
    (hchoice : higham9_1_partialPivotChoice A 0 r)
    (hpivot : A r 0 ≠ 0) :
    maxEntryNorm hm
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two A r
    hchoice hpivot i j

/-- **Theorem 9.7 / partial-pivoting growth support**, iterating the
one-step doubling recurrence for active-stage max-entry bounds. -/
theorem higham9_7_partialPivot_stageMax_le_pow_two (stageMax : ℕ → ℝ) :
    ∀ k : ℕ,
      (∀ t : ℕ, t < k → stageMax (t + 1) ≤ 2 * stageMax t) →
      stageMax k ≤ (2 : ℝ) ^ k * stageMax 0 := by
  intro k
  induction k with
  | zero =>
      intro _hstep
      simp
  | succ k ih =>
      intro hstep
      have hprev : ∀ t : ℕ, t < k → stageMax (t + 1) ≤ 2 * stageMax t := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self k))
      have hlast : stageMax (k + 1) ≤ 2 * stageMax k :=
        hstep k (Nat.lt_succ_self k)
      calc
        stageMax (Nat.succ k)
            = stageMax (k + 1) := rfl
        _ ≤ 2 * stageMax k := hlast
        _ ≤ 2 * ((2 : ℝ) ^ k * stageMax 0) :=
            mul_le_mul_of_nonneg_left (ih hprev) (by norm_num)
        _ = (2 : ℝ) ^ Nat.succ k * stageMax 0 := by
            rw [pow_succ]
            ring

/-- **Theorem 9.7 / partial-pivoting growth support**, source-shaped
`rho_n^p <= 2^(n-1)` consequence from explicit stage bounds.

The theorem deliberately keeps the algorithmic trace as hypotheses: a future
recursive GEPP formalization must supply the stage max sequence, the per-stage
doubling facts, and the final upper-factor bound. -/
theorem higham9_7_partialPivot_growthFactorEntry_le_pow_two_of_stage_bounds
    {n : ℕ} (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A) (stageMax : ℕ → ℝ)
    (hstep : ∀ t : ℕ, t < n - 1 → stageMax (t + 1) ≤ 2 * stageMax t)
    (hinit : stageMax 0 ≤ maxEntryNorm hn A)
    (hfinal : maxEntryNorm hn U ≤ stageMax (n - 1)) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  have hstage :
      stageMax (n - 1) ≤ (2 : ℝ) ^ (n - 1) * stageMax 0 :=
    higham9_7_partialPivot_stageMax_le_pow_two stageMax (n - 1) hstep
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n - 1) :=
    pow_nonneg (by norm_num) (n - 1)
  have hU :
      maxEntryNorm hn U ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
    calc
      maxEntryNorm hn U ≤ stageMax (n - 1) := hfinal
      _ ≤ (2 : ℝ) ^ (n - 1) * stageMax 0 := hstage
      _ ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A :=
          mul_le_mul_of_nonneg_left hinit hpow_nonneg
  unfold growthFactorEntry
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hU

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, a recursive exact
partial-pivoting trace that exposes the final upper-factor rows.  Each step
moves a first-column partial-pivot row into leading position, stores the pivot
row in the first row of `U`, and recursively computes the upper factor of the
first Schur complement. -/
inductive higham9_7_PartialPivotGEPPUTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A U : Fin 0 → Fin 0 → ℝ} :
      higham9_7_PartialPivotGEPPUTrace 0 A U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {r : Fin (m + 1)} {U₁ : Fin m → Fin m → ℝ}
      (hchoice : higham9_1_partialPivotChoice A 0 r)
      (hpivot : A r 0 ≠ 0)
      (hnext :
        higham9_7_PartialPivotGEPPUTrace m
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r))) U₁) :
      higham9_7_PartialPivotGEPPUTrace (m + 1) A
        (luFirstStepU
          (higham9_2_rowPermutedMatrix A (higham9_7_firstPivotRowSwap r)) U₁)

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, the exposed `U` rows
are upper triangular along the recursive trace. -/
theorem higham9_7_PartialPivotGEPPUTrace_upper_zero :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro i
      exact Fin.elim0 i
  | step _hchoice _hpivot _hnext ih =>
      intro i j hij
      by_cases hi : i = 0
      · subst i
        exact (Nat.not_lt_zero _ hij).elim
      · by_cases hj : j = 0
        · subst j
          simp [luFirstStepU, hi]
        · have hpred : (j.pred hj).val < (i.pred hi).val := by
            have hival := Fin.val_pred i hi
            have hjval := Fin.val_pred j hj
            have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega
          have hrec := ih (i.pred hi) (j.pred hj) hpred
          simpa [luFirstStepU, hi, hj] using hrec

/-- **Theorem 9.7 / partial-pivoting GEPP `U` trace**, the final upper factor
of any explicit nonsingular partial-pivoting trace satisfies the source
max-entry bound `|U_ij| <= 2^(n-1) max |A|`. -/
theorem higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two :
    ∀ {n : ℕ} {A U : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotGEPPUTrace n A U →
      ∀ (hn : 0 < n) (i j : Fin n),
        |U i j| ≤ (2 : ℝ) ^ (n - 1) * maxEntryNorm hn A := by
  intro n A U htrace
  induction htrace with
  | done =>
      intro hn
      omega
  | step hchoice hpivot hnext ih =>
      rename_i m A r U₁
      intro hn i j
      let sigma := higham9_7_firstPivotRowSwap r
      let Aperm : Fin (m + 1) → Fin (m + 1) → ℝ :=
        higham9_2_rowPermutedMatrix A sigma
      by_cases hi : i = 0
      · subst i
        have hrow : |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := by
          simpa [Aperm, higham9_2_rowPermutedMatrix, sigma,
            higham9_7_firstPivotRowSwap] using
            entry_le_maxEntryNorm (Nat.succ_pos m) A r j
        have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
          simpa using
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le m)
        have hM_nonneg : 0 ≤ maxEntryNorm (Nat.succ_pos m) A :=
          maxEntryNorm_nonneg (Nat.succ_pos m) A
        have hrow_pow :
            |Aperm 0 j| ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
          calc
            |Aperm 0 j| ≤ maxEntryNorm (Nat.succ_pos m) A := hrow
            _ = (1 : ℝ) * maxEntryNorm (Nat.succ_pos m) A := by ring
            _ ≤ (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A :=
                mul_le_mul_of_nonneg_right hpow_ge_one hM_nonneg
        simpa [Aperm, luFirstStepU] using hrow_pow
      · by_cases hj : j = 0
        · subst j
          have hnonneg :
              0 ≤ (2 : ℝ) ^ ((m + 1) - 1) *
                  maxEntryNorm (Nat.succ_pos m) A :=
            mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((m + 1) - 1))
              (maxEntryNorm_nonneg (Nat.succ_pos m) A)
          simpa [Aperm, luFirstStepU, hi] using hnonneg
        · have hm : 0 < m := by
            by_contra hm0
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
            subst hmzero
            have hival : i.val = 0 := by omega
            exact hi (Fin.ext hival)
          have hrec := ih hm (i.pred hi) (j.pred hj)
          let S : Fin m → Fin m → ℝ :=
            luFirstSchurComplement Aperm
          have hS_bound :
              maxEntryNorm hm S ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
            simpa [S, Aperm, sigma] using
              higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
                hm A r hchoice hpivot
          have hcoef_nonneg : 0 ≤ (2 : ℝ) ^ (m - 1) :=
            pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (m - 1)
          have hpow : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            have hmidx : m = (m - 1) + 1 := by omega
            calc
              (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) :=
                congrArg (fun k : ℕ => (2 : ℝ) ^ k) hmidx
              _ = (2 : ℝ) ^ (m - 1) * 2 := by
                exact pow_succ (2 : ℝ) (m - 1)
          have hpow_step :
              (2 : ℝ) ^ (m - 1) * (2 * maxEntryNorm (Nat.succ_pos m) A) =
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            rw [hpow]
            ring
          have htail :
              |U₁ (i.pred hi) (j.pred hj)| ≤
                (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := by
            calc
              |U₁ (i.pred hi) (j.pred hj)|
                  ≤ (2 : ℝ) ^ (m - 1) * maxEntryNorm hm S := by
                      simpa [S] using hrec
              _ ≤ (2 : ℝ) ^ (m - 1) *
                    (2 * maxEntryNorm (Nat.succ_pos m) A) :=
                  mul_le_mul_of_nonneg_left hS_bound hcoef_nonneg
              _ = (2 : ℝ) ^ m * maxEntryNorm (Nat.succ_pos m) A := hpow_step
          simpa [Aperm, luFirstStepU, hi, hj] using htail

/-- **Theorem 9.7**, trace-level GEPP growth theorem.  Any explicit recursive
partial-pivoting upper-factor trace satisfies Higham's standard
`rho_n^p <= 2^(n-1)` max-entry growth bound. -/
theorem higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U) :
    growthFactorEntry hn A U hAmax ≤ (2 : ℝ) ^ (n - 1) := by
  apply growthFactorEntry_le_of_entry_bound_factor hn A U ((2 : ℝ) ^ (n - 1)) hAmax
  exact higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two htrace hn

/-- **Theorem 9.7 / Wilkinson growth witness**, the source family with unit
diagonal, `-1` below the diagonal, and a final column of ones.  In Lean's
zero-based indexing, the final source column is `j = n - 1`. -/
noncomputable def higham9_7_wilkinsonGrowthMatrix {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = i.val ∨ j.val = n - 1 then 1
    else if j.val < i.val then -1
    else 0

/-- **Theorem 9.7 / Wilkinson growth witness**, the exact unit lower factor
for the displayed Wilkinson matrix. -/
noncomputable def higham9_7_wilkinsonGrowthL {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j => if j.val = i.val then 1 else if j.val < i.val then -1 else 0

/-- **Theorem 9.7 / Wilkinson growth witness**, the exact upper factor.  The
final column contains the powers `2^i`, so its last entry is `2^(n-1)`. -/
noncomputable def higham9_7_wilkinsonGrowthU {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then (2 : ℝ) ^ i.val
    else if j.val = i.val then 1
    else 0

/-- **Theorem 9.7 / scaled Wilkinson active-stage upper factor**, the upper
factor for a reduced active stage whose final column has value `scale`. -/
noncomputable def higham9_7_wilkinsonGrowthStageU (scale : ℝ) {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then scale * (2 : ℝ) ^ i.val
    else if j.val = i.val then 1
    else 0

/-- The scaled active-stage upper factor with scale one is the displayed
Wilkinson witness upper factor. -/
theorem higham9_7_wilkinsonGrowthStageU_one {n : ℕ} :
    higham9_7_wilkinsonGrowthStageU 1 (n := n) =
      higham9_7_wilkinsonGrowthU (n := n) := by
  ext i j
  simp [higham9_7_wilkinsonGrowthStageU, higham9_7_wilkinsonGrowthU]

/-- **Theorem 9.7 / Wilkinson growth witness**, active-stage version of the
displayed family.  The parameter `scale` is the value in the final active
column; a no-pivot Schur step doubles it. -/
noncomputable def higham9_7_wilkinsonGrowthStageMatrix (scale : ℝ) {n : ℕ} :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if j.val = n - 1 then scale
    else if j.val = i.val then 1
    else if j.val < i.val then -1
    else 0

/-- The initial scaled-stage matrix with scale one is the displayed Wilkinson
growth witness. -/
theorem higham9_7_wilkinsonGrowthStageMatrix_one {n : ℕ} :
    higham9_7_wilkinsonGrowthStageMatrix 1 (n := n) =
      higham9_7_wilkinsonGrowthMatrix (n := n) := by
  funext i j
  unfold higham9_7_wilkinsonGrowthStageMatrix higham9_7_wilkinsonGrowthMatrix
  by_cases hlast : j.val = n - 1
  · simp [hlast]
  · simp [hlast]

/-- **Theorem 9.7 / no-interchange support**, at every nontrivial Wilkinson
stage the leading row is an admissible partial-pivoting choice.  Thus the
source's "no interchanges" claim reduces to iterating these displayed stage
matrices. -/
theorem higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero {m : ℕ}
    (scale : ℝ) :
    higham9_1_partialPivotChoice
      (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 2)) 0 0 := by
  constructor
  · simp
  · intro i _hi
    unfold higham9_7_wilkinsonGrowthStageMatrix
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · have h0i_ne : ¬ (0 : ℕ) = i.val := by omega
      have h0_lt_i : (0 : ℕ) < i.val := by omega
      simp [h0i_ne, h0_lt_i]

/-- **Theorem 9.7 / reduced-matrix support**, the first no-pivot Schur
complement of a Wilkinson active-stage matrix is the next active-stage matrix
with doubled final column. -/
theorem higham9_7_wilkinsonGrowthStage_firstSchurComplement {m : ℕ}
    (scale : ℝ) :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 2)) =
      higham9_7_wilkinsonGrowthStageMatrix (2 * scale) (n := m + 1) := by
  funext i j
  unfold luFirstSchurComplement higham9_7_wilkinsonGrowthStageMatrix
  by_cases hlast : j.succ.val = m + 2 - 1
  · have hlast_m : j.val = m := by
      have hj : j.succ.val = j.val + 1 := rfl
      omega
    simp [hlast_m]
    ring
  · have hlast_m : ¬ j.val = m := by
      intro hjlast
      have hj : j.succ.val = j.val + 1 := rfl
      exact hlast (by omega)
    simp [hlast_m]

/-- The power-of-two stage form of the Wilkinson Schur-complement doubling
identity. -/
theorem higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement {m t : ℕ} :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := m + 2)) =
      higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ (t + 1)) (n := m + 1) := by
  rw [higham9_7_wilkinsonGrowthStage_firstSchurComplement]
  rw [pow_succ]
  ring_nf

/-- **Theorem 9.7 / no-interchange GEPP trace**, a compact exact-arithmetic
trace predicate for partial pivoting when every active step chooses row zero.
This records the source "no row interchanges" route without modeling floating
point arithmetic. -/
inductive higham9_7_PartialPivotNoInterchangeTrace :
    ℕ → (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {t : ℕ} {A : Fin 0 → Fin 0 → ℝ} :
      higham9_7_PartialPivotNoInterchangeTrace t 0 A
  | step {t m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hchoice : higham9_1_partialPivotChoice A 0 0)
      (hpivot : A 0 0 ≠ 0)
      (hnext :
        higham9_7_PartialPivotNoInterchangeTrace (t + 1) m
          (luFirstSchurComplement A)) :
      higham9_7_PartialPivotNoInterchangeTrace t (m + 1) A

/-- **Theorem 9.7 / no-interchange support**, row zero is a valid
partial-pivoting choice for every nonempty scaled Wilkinson active stage. -/
theorem higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ {m : ℕ}
    (scale : ℝ) :
    higham9_1_partialPivotChoice
      (higham9_7_wilkinsonGrowthStageMatrix scale (n := m + 1)) 0 0 := by
  cases m with
  | zero =>
      constructor
      · simp
      · intro i _hi
        fin_cases i
        simp
  | succ m =>
      simpa using
        higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero (m := m) scale

/-- **Theorem 9.7 / no-interchange support**, the row-zero pivot in every
power-of-two scaled Wilkinson active stage is nonzero. -/
theorem higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero {m t : ℕ} :
    higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t)
      (0 : Fin (m + 1)) 0 ≠ 0 := by
  cases m with
  | zero =>
      simp [higham9_7_wilkinsonGrowthStageMatrix]
  | succ m =>
      simp [higham9_7_wilkinsonGrowthStageMatrix]

/-- **Theorem 9.7 / no-interchange support**, the Schur-complement doubling
identity, including the `1 by 1` terminal step. -/
theorem higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ
    {m t : ℕ} :
    luFirstSchurComplement
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := m + 1)) =
      higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ (t + 1)) (n := m) := by
  cases m with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ m =>
      simpa using
        higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement (m := m) (t := t)

/-- **Theorem 9.7 / Wilkinson no-interchange GEPP trace**, every power-of-two
scaled active-stage matrix follows the no-row-interchange partial-pivoting
trace.  This closes the source trace for the displayed Wilkinson growth family;
the separate extremal characterization remains open. -/
theorem higham9_7_wilkinsonGrowthStage_noInterchangeTrace :
    ∀ n t : ℕ,
      higham9_7_PartialPivotNoInterchangeTrace t n
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := n))
  | 0, t => higham9_7_PartialPivotNoInterchangeTrace.done
  | m + 1, t =>
      by
        refine higham9_7_PartialPivotNoInterchangeTrace.step
          (higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ
            (m := m) ((2 : ℝ) ^ t))
          (higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero (m := m) (t := t))
          ?_
        rw [higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ]
        exact higham9_7_wilkinsonGrowthStage_noInterchangeTrace m (t + 1)

/-- **Theorem 9.7 / Wilkinson no-interchange GEPP trace**, source-facing
version for the displayed initial matrix. -/
theorem higham9_7_wilkinsonGrowth_noInterchangeTrace (n : ℕ) :
    higham9_7_PartialPivotNoInterchangeTrace 0 n
      (higham9_7_wilkinsonGrowthMatrix (n := n)) := by
  simpa [higham9_7_wilkinsonGrowthStageMatrix_one] using
    higham9_7_wilkinsonGrowthStage_noInterchangeTrace n 0

/-- Uniform max-entry bound for a scaled Wilkinson active-stage matrix. -/
theorem higham9_7_wilkinsonGrowthStage_entry_abs_le_scale {n : ℕ}
    {scale : ℝ} (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale)
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthStageMatrix scale i j| ≤ scale := by
  unfold higham9_7_wilkinsonGrowthStageMatrix
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg hscale_nonneg]
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      exact hscale_one
    · by_cases hlt : j.val < i.val
      · simp [hlast, hdiag, hlt]
        exact hscale_one
      · simp [hlast, hdiag, hlt, hscale_nonneg]

/-- A scaled Wilkinson active-stage matrix has max-entry norm equal to its
final-column scale whenever that scale is at least one. -/
theorem higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n)) =
      scale := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthStage_entry_abs_le_scale
      hscale_nonneg hscale_one i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthStageMatrix scale
            (⟨0, hn⟩ : Fin n) last| = scale := by
      simp [higham9_7_wilkinsonGrowthStageMatrix, last,
        abs_of_nonneg hscale_nonneg]
    have hle :=
      entry_le_maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
        (⟨0, hn⟩ : Fin n) last
    simpa [hentry] using hle

/-- At Wilkinson stage `t`, the active matrix has max-entry norm `2^t`. -/
theorem higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_pow {n t : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageMatrix ((2 : ℝ) ^ t) (n := n)) =
      (2 : ℝ) ^ t := by
  exact higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) t)
    (by
      have hpow : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ t :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le t)
      simpa using hpow)

/-- The lower factor row of the Wilkinson witness satisfies the final-column
power identity `2^i - sum_{k<i} 2^k = 1`. -/
theorem higham9_7_wilkinsonGrowthL_two_pow_sum {n : ℕ} (i : Fin n) :
    (∑ k : Fin n, higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) = 1 := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.sum_univ_succ]
          simp [higham9_7_wilkinsonGrowthL]
      | succ i =>
          rw [Fin.sum_univ_succ]
          have htail :
              (∑ k : Fin n,
                  higham9_7_wilkinsonGrowthL (Fin.succ i) k.succ *
                    (2 : ℝ) ^ k.succ.val) =
                2 *
                  (∑ k : Fin n,
                    higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k.val = i.val
            · simp [higham9_7_wilkinsonGrowthL, hki, pow_succ]
              ring
            · by_cases hklt : k.val < i.val
              · simp [higham9_7_wilkinsonGrowthL, hki, hklt, pow_succ]
                ring
              · simp [higham9_7_wilkinsonGrowthL, hki, hklt, pow_succ]
          calc
            higham9_7_wilkinsonGrowthL (Fin.succ i) 0 *
                  (2 : ℝ) ^ (0 : Fin (n + 1)).val +
                (∑ x : Fin n,
                  higham9_7_wilkinsonGrowthL (Fin.succ i) x.succ *
                    (2 : ℝ) ^ x.succ.val)
                = (-1 : ℝ) + 2 * 1 := by
                    rw [htail, ih i]
                    simp [higham9_7_wilkinsonGrowthL]
            _ = 1 := by norm_num

/-- **Theorem 9.7 / scaled Wilkinson active-stage witness**, exact LU
certificate for every scaled active-stage matrix.  This is the algebraic
certificate behind the source no-interchange stage recurrence; the executable
partial-pivoting trace remains recorded separately. -/
theorem higham9_7_wilkinsonGrowthStage_lu (n : ℕ) (scale : ℝ) :
    LUFactSpec n (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
      (higham9_7_wilkinsonGrowthL (n := n))
      (higham9_7_wilkinsonGrowthStageU scale (n := n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [higham9_7_wilkinsonGrowthL]
  · intro i j hij
    have hne : j.val ≠ i.val := by omega
    have hnotlt : ¬ j.val < i.val := by omega
    simp [higham9_7_wilkinsonGrowthL, hne, hnotlt]
  · intro i j hij
    have hnotlast : j.val ≠ n - 1 := by
      intro hlast
      have hle : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
      omega
    have hne : j.val ≠ i.val := by omega
    simp [higham9_7_wilkinsonGrowthStageU, hnotlast, hne]
  · intro i j
    by_cases hlast : j.val = n - 1
    · calc
        (∑ k : Fin n,
            higham9_7_wilkinsonGrowthL i k *
              higham9_7_wilkinsonGrowthStageU scale k j)
            = scale * ∑ k : Fin n,
                higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                simp [higham9_7_wilkinsonGrowthStageU, hlast, mul_left_comm]
        _ = scale * 1 := by rw [higham9_7_wilkinsonGrowthL_two_pow_sum i]
        _ = higham9_7_wilkinsonGrowthStageMatrix scale i j := by
            simp [higham9_7_wilkinsonGrowthStageMatrix, hlast]
    · have hsum :
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthStageU scale k j) =
            higham9_7_wilkinsonGrowthL i j := by
        calc
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthStageU scale k j)
              = ∑ k : Fin n,
                  if k = j then higham9_7_wilkinsonGrowthL i j else 0 := by
                  apply Finset.sum_congr rfl
                  intro k _
                  by_cases hkj : k = j
                  · subst hkj
                    simp [higham9_7_wilkinsonGrowthStageU, hlast]
                  · have hjk : j.val ≠ k.val := by
                      intro hv
                      exact hkj (Fin.ext hv.symm)
                    simp [higham9_7_wilkinsonGrowthStageU, hlast, hjk, hkj]
          _ = higham9_7_wilkinsonGrowthL i j := by simp
      rw [hsum]
      simp [higham9_7_wilkinsonGrowthStageMatrix, higham9_7_wilkinsonGrowthL,
        hlast]

/-- Every entry of the scaled active-stage upper factor is bounded by
`scale * 2^(n-1)` whenever `scale >= 1`. -/
theorem higham9_7_wilkinsonGrowthStageU_entry_abs_le_scale_pow {n : ℕ}
    {scale : ℝ} (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale)
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthStageU scale i j| ≤
      scale * (2 : ℝ) ^ (n - 1) := by
  unfold higham9_7_wilkinsonGrowthStageU
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg (mul_nonneg hscale_nonneg
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i.val))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.le_sub_one_of_lt i.isLt)) hscale_nonneg
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) := by
        simpa using
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le (n - 1))
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ scale * (2 : ℝ) ^ (n - 1) :=
          mul_le_mul hscale_one hpow (by norm_num) hscale_nonneg
    · simp [hlast, hdiag, hscale_nonneg]

/-- The scaled active-stage upper factor has max-entry norm
`scale * 2^(n-1)` whenever `scale >= 1`. -/
theorem higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthStageU scale (n := n)) =
      scale * (2 : ℝ) ^ (n - 1) := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthStageU_entry_abs_le_scale_pow
      hscale_nonneg hscale_one i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthStageU scale last last| =
          scale * (2 : ℝ) ^ (n - 1) := by
      simp [higham9_7_wilkinsonGrowthStageU, last,
        abs_of_nonneg (mul_nonneg hscale_nonneg
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1)))]
    have hle :=
      entry_le_maxEntryNorm hn
        (higham9_7_wilkinsonGrowthStageU scale (n := n)) last last
    simpa [hentry] using hle

/-- **Theorem 9.7 / scaled active-stage growth**, every scaled active-stage
Wilkinson matrix has exact max-entry growth `2^(n-1)` for its scaled upper
factor, provided the scale is at least one. -/
theorem higham9_7_wilkinsonGrowthStage_growthFactorEntry_eq_pow {n : ℕ}
    (hn : 0 < n) {scale : ℝ}
    (hscale_nonneg : 0 ≤ scale) (hscale_one : 1 ≤ scale) :
    growthFactorEntry hn
        (higham9_7_wilkinsonGrowthStageMatrix scale (n := n))
        (higham9_7_wilkinsonGrowthStageU scale (n := n))
        (by
          rw [higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
            hscale_nonneg hscale_one]
          linarith) =
      (2 : ℝ) ^ (n - 1) := by
  have hscale_pos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale_one
  unfold growthFactorEntry
  rw [higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow hn
      hscale_nonneg hscale_one,
    higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale hn
      hscale_nonneg hscale_one]
  field_simp [ne_of_gt hscale_pos]

/-- **Theorem 9.7 / Wilkinson growth witness**, exact LU certificate for the
displayed matrix family.  This is the algebraic witness behind the source
statement that the final column doubles under the no-interchange GEPP route;
the recursive no-interchange trace is closed separately by
`higham9_7_wilkinsonGrowth_noInterchangeTrace`. -/
theorem higham9_7_wilkinsonGrowth_lu (n : ℕ) :
    LUFactSpec n (higham9_7_wilkinsonGrowthMatrix (n := n))
      (higham9_7_wilkinsonGrowthL (n := n))
      (higham9_7_wilkinsonGrowthU (n := n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [higham9_7_wilkinsonGrowthL]
  · intro i j hij
    have hne : j.val ≠ i.val := by omega
    have hnotlt : ¬ j.val < i.val := by omega
    simp [higham9_7_wilkinsonGrowthL, hne, hnotlt]
  · intro i j hij
    have hnotlast : j.val ≠ n - 1 := by
      intro hlast
      have hle : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
      omega
    have hne : j.val ≠ i.val := by omega
    simp [higham9_7_wilkinsonGrowthU, hnotlast, hne]
  · intro i j
    by_cases hlast : j.val = n - 1
    · calc
        (∑ k : Fin n,
            higham9_7_wilkinsonGrowthL i k *
              higham9_7_wilkinsonGrowthU k j)
            = ∑ k : Fin n,
                higham9_7_wilkinsonGrowthL i k * (2 : ℝ) ^ k.val := by
                apply Finset.sum_congr rfl
                intro k _
                simp [higham9_7_wilkinsonGrowthU, hlast]
        _ = 1 := higham9_7_wilkinsonGrowthL_two_pow_sum i
        _ = higham9_7_wilkinsonGrowthMatrix i j := by
            simp [higham9_7_wilkinsonGrowthMatrix, hlast]
    · have hsum :
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthU k j) =
            higham9_7_wilkinsonGrowthL i j := by
        calc
          (∑ k : Fin n,
              higham9_7_wilkinsonGrowthL i k *
                higham9_7_wilkinsonGrowthU k j)
              = ∑ k : Fin n,
                  if k = j then higham9_7_wilkinsonGrowthL i j else 0 := by
                  apply Finset.sum_congr rfl
                  intro k _
                  by_cases hkj : k = j
                  · subst hkj
                    simp [higham9_7_wilkinsonGrowthU, hlast]
                  · have hjk : j.val ≠ k.val := by
                      intro hv
                      exact hkj (Fin.ext hv.symm)
                    simp [higham9_7_wilkinsonGrowthU, hlast, hjk, hkj]
          _ = higham9_7_wilkinsonGrowthL i j := by simp
      rw [hsum]
      simp [higham9_7_wilkinsonGrowthMatrix, higham9_7_wilkinsonGrowthL, hlast]

/-- Every entry of the Wilkinson growth witness has absolute value at most
one. -/
theorem higham9_7_wilkinsonGrowthMatrix_entry_abs_le_one {n : ℕ}
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthMatrix i j| ≤ 1 := by
  unfold higham9_7_wilkinsonGrowthMatrix
  by_cases hmain : j.val = i.val ∨ j.val = n - 1
  · simp [hmain]
  · by_cases hlt : j.val < i.val
    · simp [hmain, hlt]
    · simp [hmain, hlt]

/-- The Wilkinson growth witness has source max-entry norm one. -/
theorem higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one {n : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n)) = 1 := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthMatrix_entry_abs_le_one i j
  · have hentry :
        |higham9_7_wilkinsonGrowthMatrix (⟨0, hn⟩ : Fin n) ⟨0, hn⟩| = 1 := by
      simp [higham9_7_wilkinsonGrowthMatrix]
    have hle :=
      entry_le_maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n))
        (⟨0, hn⟩ : Fin n) ⟨0, hn⟩
    simpa [hentry] using hle

/-- The Wilkinson growth witness has positive source max-entry norm. -/
theorem higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos {n : ℕ}
    (hn : 0 < n) :
    0 < maxEntryNorm hn (higham9_7_wilkinsonGrowthMatrix (n := n)) := by
  simp [higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one hn]

/-- Every entry of the upper factor is bounded by the final-column value
`2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowthU_entry_abs_le_pow {n : ℕ}
    (i j : Fin n) :
    |higham9_7_wilkinsonGrowthU i j| ≤ (2 : ℝ) ^ (n - 1) := by
  unfold higham9_7_wilkinsonGrowthU
  by_cases hlast : j.val = n - 1
  · simp [hlast, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i.val)]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_sub_one_of_lt i.isLt)
  · by_cases hdiag : j.val = i.val
    · have hilast : i.val ≠ n - 1 := by
        intro hi
        exact hlast (hdiag.trans hi)
      simp [hdiag, hilast]
      have hpow : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ (n - 1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le (n - 1))
      simpa using hpow
    · simp [hlast, hdiag]

/-- The exact upper factor of the Wilkinson witness has max-entry norm
`2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow {n : ℕ}
    (hn : 0 < n) :
    maxEntryNorm hn (higham9_7_wilkinsonGrowthU (n := n)) =
      (2 : ℝ) ^ (n - 1) := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    exact higham9_7_wilkinsonGrowthU_entry_abs_le_pow i j
  · let last : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩
    have hentry :
        |higham9_7_wilkinsonGrowthU last last| = (2 : ℝ) ^ (n - 1) := by
      simp [higham9_7_wilkinsonGrowthU, last,
        abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))]
    have hle :=
      entry_le_maxEntryNorm hn (higham9_7_wilkinsonGrowthU (n := n)) last last
    simpa [hentry] using hle

/-- **Theorem 9.7 / Wilkinson growth witness**, the displayed family attains
the max-entry growth value `2^(n-1)` for the exact upper factor above. -/
theorem higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow {n : ℕ}
    (hn : 0 < n) :
    growthFactorEntry hn (higham9_7_wilkinsonGrowthMatrix (n := n))
        (higham9_7_wilkinsonGrowthU (n := n))
        (higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn) =
      (2 : ℝ) ^ (n - 1) := by
  unfold growthFactorEntry
  rw [higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow hn,
    higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one hn]
  ring

/-- **Theorem 9.7**, source-facing Wilkinson attainability package.  The
displayed Wilkinson family has an exact LU certificate, follows the closed
no-interchange partial-pivoting trace, and attains the bound `2^(n-1)`. -/
theorem higham9_7_wilkinsonGrowth_attains_partialPivoting_bound {n : ℕ}
    (hn : 0 < n) :
    ∃ A L U : Fin n → Fin n → ℝ,
    ∃ hAmax : 0 < maxEntryNorm hn A,
      LUFactSpec n A L U ∧
      higham9_7_PartialPivotNoInterchangeTrace 0 n A ∧
      growthFactorEntry hn A U hAmax = (2 : ℝ) ^ (n - 1) := by
  refine ⟨higham9_7_wilkinsonGrowthMatrix (n := n),
    higham9_7_wilkinsonGrowthL (n := n),
    higham9_7_wilkinsonGrowthU (n := n),
    higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_pos hn, ?_, ?_, ?_⟩
  · exact higham9_7_wilkinsonGrowth_lu n
  · exact higham9_7_wilkinsonGrowth_noInterchangeTrace n
  · exact higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow hn

/-- **Equation (9.2a)**, source-facing exact permuted LU certificate
`PA = LU`. -/
abbrev higham9_2_PermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n) : Prop :=
  PermutedLUFactSpec n A L U sigma

/-- **Equation (9.2a)**, a source `PA = LU` certificate is an ordinary exact LU
certificate for the row-permuted matrix. -/
theorem higham9_2_permutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    LUFactSpec n (higham9_2_rowPermutedMatrix A sigma) L U where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  product_eq := by
    intro i j
    simpa [higham9_2_rowPermutedMatrix] using hLU.product_eq i j

/-- **Equation (9.2a)**, determinant-pivot product for an explicit
row-permuted LU certificate `PA = LU`. -/
theorem higham9_2_permutedLUFactSpec_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A sigma) :
          Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU).det_eq_prod_U_diag

/-- **Equation (9.2a)**, nonsingularity consequence for an explicit
row-permuted LU certificate. -/
theorem higham9_2_permutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A sigma) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU).det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.3 / equation (9.2a)**, source-facing permuted LU backward-error
certificate. -/
abbrev higham9_2_PermutedLUBackwardError (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (ε : ℝ) : Prop :=
  PermutedLUBackwardError n A L_hat U_hat sigma ε

/-- **Theorem 9.3 / equation (9.2a)**, a pivoted backward-error certificate is
an ordinary LU backward-error certificate for the row-permuted matrix `PA`. -/
theorem higham9_2_permutedLUBackwardError_to_LUBackwardError {n : ℕ}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    {ε : ℝ}
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma ε) :
    LUBackwardError n (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat ε where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    simpa [higham9_2_rowPermutedMatrix] using hLU.backward_bound i j

/-- **Theorem 9.3 / equation (9.2a)**, exact row-pivoted certificates are
zero-coefficient pivoted backward-error certificates.  This is an exact-factor
adapter; it does not assert that a floating-point pivoting loop produced the
certificate. -/
theorem higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    higham9_2_PermutedLUBackwardError n A L U sigma 0 where
  perm := hLU.perm
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    calc
      |∑ k : Fin n, L i k * U k j - A (sigma i) j|
          = |A (sigma i) j - A (sigma i) j| := by
              rw [hLU.product_eq i j]
      _ ≤ 0 * ∑ k : Fin n, |L i k| * |U k j| := by simp

/-- **Theorem 9.3 / equation (9.2a)**, exact row-pivoted certificates can be
viewed at the standard `gamma_n` perturbation level.  The residual is exactly
zero, so this is a weakening of the exact certificate rather than a computed
floating-point trace construction. -/
theorem higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    higham9_2_PermutedLUBackwardError n A L U sigma (gamma fp n) where
  perm := hLU.perm
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    have hzero :
        |∑ k : Fin n, L i k * U k j - A (sigma i) j| = 0 := by
      rw [hLU.product_eq i j]
      simp
    rw [hzero]
    exact mul_nonneg (gamma_nonneg fp hn)
      (Finset.sum_nonneg
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- **Equation (9.2a)**, row permutations preserve Higham's max-entry norm. -/
theorem higham9_2_rowPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) :
    maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma) = maxEntryNorm hn A := by
  classical
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hsigma
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham9_2_rowPermutedMatrix A sigma i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_rowPermutedMatrix] using
      entry_le_maxEntryNorm hn A (sigma i) j
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    simpa [higham9_2_rowPermutedMatrix, hsigma_symm] using
      entry_le_maxEntryNorm hn (higham9_2_rowPermutedMatrix A sigma)
        (eSigma.symm i) j

/-- **Equation (9.2a)**, row permutations preserve the matrix infinity norm. -/
theorem higham9_2_rowPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) :
    infNorm (higham9_2_rowPermutedMatrix A sigma) = infNorm A := by
  classical
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hsigma
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simpa [higham9_2_rowPermutedMatrix] using row_sum_le_infNorm A (sigma i)
    · exact infNorm_nonneg A
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hsigma_symm : sigma (eSigma.symm i) = i := by
        change eSigma (eSigma.symm i) = i
        exact Equiv.apply_symm_apply eSigma i
      simpa [higham9_2_rowPermutedMatrix, hsigma_symm] using
        row_sum_le_infNorm (higham9_2_rowPermutedMatrix A sigma) (eSigma.symm i)
    · exact infNorm_nonneg (higham9_2_rowPermutedMatrix A sigma)

/-- **Equation (9.1)**, determinant-pivot product for an exact LU
certificate: if `A = L U` with unit lower triangular `L` and upper triangular
`U`, then `det(A)` is the product of the diagonal pivots of `U`.  Theorem 9.1's
existence/uniqueness direction remains a separate determinant-integrated LU
target. -/
theorem higham9_1_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  hLU.det_eq_prod_U_diag

/-- **Equation (9.1)**, nonzero-pivot consequence of the determinant product:
an exact LU certificate is nonsingular exactly when all diagonal pivots of `U`
are nonzero. -/
theorem higham9_1_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  hLU.det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.1 support**, first Schur complement for the exact no-pivot LU
existence induction. -/
noncomputable abbrev higham9_1_firstSchurComplement {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  luFirstSchurComplement A

/-- **Theorem 9.1 base certificate**, every `1 by 1` matrix has the explicit
unit-lower/upper LU certificate with lower factor `[1]` and upper factor equal
to the source matrix. -/
theorem higham9_1_LUFactSpec_one_explicit
    (A : Fin 1 → Fin 1 → ℝ) :
    LUFactSpec 1 A (fun _ _ => 1) A := by
  refine
    { L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      product_eq := ?_ }
  · intro i
    fin_cases i
    rfl
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (Nat.lt_irrefl 0 hij).elim
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (Nat.lt_irrefl 0 hij).elim
  · intro i j
    fin_cases i
    fin_cases j
    simp

/-- **Theorem 9.1 support**, one exact no-pivot LU construction step.
If the first pivot is nonzero and the first Schur complement has an exact
unit-lower/upper LU certificate, then the original matrix has an exact
unit-lower/upper LU certificate.  This is the local induction step toward the
source existence theorem from nonsingular leading principal submatrices. -/
theorem higham9_1_lu_exists_of_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℝ}
    (hS : LUFactSpec m (higham9_1_firstSchurComplement A) L₁ U₁) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → ℝ,
      LUFactSpec (m + 1) A L U :=
  LUFactSpec.of_firstSchurComplement hpivot hS

/-- **Theorem 9.1 support: Schur-complement determinant identity.**
For a nonzero pivot `A 0 0`, the determinant factors through the first
Schur complement: `det A = A 0 0 · det (luFirstSchurComplement A)`.
Proof: one exact elimination step `E · A = R` with `E` unit lower
triangular and `R` having a zero first column below the pivot, then
first-column Laplace expansion of `R`. -/
theorem higham9_1_det_eq_pivot_mul_firstSchurComplement_det {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (hpiv : A 0 0 ≠ 0) :
    (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det
      = A 0 0 *
        (Matrix.of (luFirstSchurComplement A) : Matrix (Fin m) (Fin m) ℝ).det := by
  classical
  set E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j : Fin (m + 1) =>
      if i = j then (1 : ℝ) else if j = 0 then -(A i 0 / A 0 0) else 0) with hE
  set R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of (fun i j : Fin (m + 1) =>
      if i = 0 then A 0 j
      else if j = 0 then 0 else A i j - A i 0 * A 0 j / A 0 0) with hR
  have hEtri : Matrix.BlockTriangular E OrderDual.toDual := by
    intro a b hab
    have hab' : a.val < b.val := by simpa using hab
    have hne : a ≠ b := fun h => by rw [h] at hab'; omega
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hab'
      simp at hab'
    simp only [hE, Matrix.of_apply, if_neg hne, if_neg hb0]
  have hEdet : E.det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ hEtri]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp [hE]
  have hprod : E * Matrix.of A = R := by
    ext i j
    simp only [Matrix.mul_apply, hE, hR, Matrix.of_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Finset.sum_eq_single (0 : Fin (m + 1))
        (fun t _ ht => by
          rw [if_neg (Ne.symm ht), if_neg ht, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · have hne0i : (0 : Fin (m + 1)) ≠ i := Ne.symm hi
      rw [← Finset.sum_subset
        (Finset.subset_univ ({0, i} : Finset (Fin (m + 1))))
        (fun t _ ht => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
          rw [if_neg (fun h => ht.2 h.symm), if_neg ht.1, zero_mul])]
      rw [Finset.sum_pair hne0i]
      by_cases hj : j = 0
      · subst hj
        simp [hi]
        field_simp
        ring
      · simp [hi, hj]
        field_simp
        ring
  have hdetR : (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det = R.det := by
    calc (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det
        = E.det * (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det := by
          rw [hEdet, one_mul]
      _ = (E * Matrix.of A).det := (Matrix.det_mul _ _).symm
      _ = R.det := by rw [hprod]
  have hsub : R.submatrix (Fin.succAbove 0) Fin.succ
      = (Matrix.of (luFirstSchurComplement A) : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp only [Matrix.submatrix_apply, hR, Matrix.of_apply, Fin.zero_succAbove,
      luFirstSchurComplement]
    rw [if_neg (Fin.succ_ne_zero i), if_neg (Fin.succ_ne_zero j)]
  have hRdet : R.det
      = A 0 0 *
        (Matrix.of (luFirstSchurComplement A) : Matrix (Fin m) (Fin m) ℝ).det := by
    rw [Matrix.det_succ_column_zero]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))
      (fun t _ ht => by
        have h1 : R t 0 = 0 := by
          simp [hR, ht]
        rw [h1]
        ring)
      (fun h => absurd (Finset.mem_univ _) h)]
    have hR00 : R 0 0 = A 0 0 := by
      simp [hR]
    rw [hR00, hsub]
    simp
  rw [hdetR, hRdet]

/-- **Theorem 9.1 support**: the first Schur complement commutes with taking
leading principal blocks. -/
theorem higham9_1_firstSchurComplement_leadingSubmatrix_comm {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {k : ℕ} (hk1 : k + 1 ≤ m + 1) (hk : k ≤ m) (i j : Fin k) :
    luFirstSchurComplement
      (fun a b : Fin (k + 1) => A (Fin.castLE hk1 a) (Fin.castLE hk1 b)) i j
      = luFirstSchurComplement A (Fin.castLE hk i) (Fin.castLE hk j) := by
  simp only [luFirstSchurComplement]
  have hsi : Fin.castLE hk1 i.succ = (Fin.castLE hk i).succ := Fin.ext (by simp)
  have hsj : Fin.castLE hk1 j.succ = (Fin.castLE hk j).succ := Fin.ext (by simp)
  have h0 : Fin.castLE hk1 (0 : Fin (k + 1)) = (0 : Fin (m + 1)) :=
    Fin.ext (by simp)
  rw [hsi, hsj, h0]

/-- **Theorem 9.1 support: leading-minor Schur identity.**  For a nonzero
pivot, the `(k+1)`-st leading minor of `A` is the pivot times the `k`-th
leading minor of the first Schur complement. -/
theorem higham9_1_leadingSubmatrix_det_eq_pivot_mul_schur {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (hpiv : A 0 0 ≠ 0)
    {k : ℕ} (hk1 : k + 1 ≤ m + 1) (hk : k ≤ m) :
    Matrix.det ((Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).submatrix
        (Fin.castLE hk1) (Fin.castLE hk1))
      = A 0 0 * Matrix.det
          ((Matrix.of (luFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℝ).submatrix
            (Fin.castLE hk) (Fin.castLE hk)) := by
  have h0 : Fin.castLE hk1 (0 : Fin (k + 1)) = (0 : Fin (m + 1)) :=
    Fin.ext (by simp)
  have hpiv' : (fun a b : Fin (k + 1) =>
      A (Fin.castLE hk1 a) (Fin.castLE hk1 b)) 0 0 ≠ 0 := by
    simpa [h0] using hpiv
  have h1 := higham9_1_det_eq_pivot_mul_firstSchurComplement_det
    (fun a b : Fin (k + 1) => A (Fin.castLE hk1 a) (Fin.castLE hk1 b)) hpiv'
  have hL : (Matrix.of (fun a b : Fin (k + 1) =>
      A (Fin.castLE hk1 a) (Fin.castLE hk1 b))
      : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
      = (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).submatrix
          (Fin.castLE hk1) (Fin.castLE hk1) := rfl
  have hS : (Matrix.of (luFirstSchurComplement
      (fun a b : Fin (k + 1) => A (Fin.castLE hk1 a) (Fin.castLE hk1 b)))
      : Matrix (Fin k) (Fin k) ℝ)
      = (Matrix.of (luFirstSchurComplement A) :
          Matrix (Fin m) (Fin m) ℝ).submatrix
          (Fin.castLE hk) (Fin.castLE hk) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    exact higham9_1_firstSchurComplement_leadingSubmatrix_comm A hk1 hk i j
  rw [hL, hS] at h1
  rw [h1]
  congr 1

/-- **Theorem 9.1 (existence direction): LU existence from nonvanishing
leading principal minors.**  If every leading principal minor of `A` is
nonzero, then `A` has an exact unit-lower/upper LU certificate.  This is the
classical existence statement of Theorem 9.1, proved by induction on the
dimension through the first Schur complement (whose leading minors are
nonzero by the leading-minor Schur identity). -/
theorem higham9_1_lu_exists_of_leading_minors_ne_zero : ∀ {n : ℕ}
    (A : Fin n → Fin n → ℝ),
    (∀ (k : ℕ) (hk : k ≤ n),
      Matrix.det ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
        (Fin.castLE hk) (Fin.castLE hk)) ≠ 0) →
    ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _
      exact ⟨A, A, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩⟩
  | succ m ih =>
      intro A hminors
      have h1le : (1 : ℕ) ≤ m + 1 := by omega
      have hpiv : A 0 0 ≠ 0 := by
        have h1 := hminors 1 h1le
        rw [Matrix.det_fin_one] at h1
        have h0 : Fin.castLE h1le (0 : Fin 1) = (0 : Fin (m + 1)) :=
          Fin.ext (by simp)
        simpa [h0] using h1
      have hSminors : ∀ (k : ℕ) (hk : k ≤ m),
          Matrix.det ((Matrix.of (luFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℝ).submatrix
            (Fin.castLE hk) (Fin.castLE hk)) ≠ 0 := by
        intro k hk
        have hk1 : k + 1 ≤ m + 1 := by omega
        have hid := higham9_1_leadingSubmatrix_det_eq_pivot_mul_schur
          A hpiv hk1 hk
        have hnz := hminors (k + 1) hk1
        rw [hid] at hnz
        exact (mul_ne_zero_iff.mp hnz).2
      obtain ⟨L₁, U₁, hS⟩ := ih (luFirstSchurComplement A) hSminors
      exact higham9_1_lu_exists_of_firstSchurComplement hpiv hS

/-- Sum truncation over a leading `Fin k` prefix when all later terms vanish.
This is the small finite-sum adapter used to pass exact LU certificates to
leading principal blocks. -/
private lemma sum_fin_eq_sum_castLE_of_eq_zero {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) (hzero : ∀ r : Fin n, k ≤ r.val → f r = 0) :
    (∑ r : Fin n, f r) = ∑ r : Fin k, f (Fin.castLE hk r) := by
  classical
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hsmall :
      (∑ x ∈ Finset.range k,
        if hx : x < k then f (Fin.castLE hk ⟨x, hx⟩) else 0) =
        ∑ x ∈ Finset.range k, if hx : x < n then f ⟨x, hx⟩ else 0 := by
    apply Finset.sum_congr rfl
    intro x hxmem
    have hxk : x < k := by
      simpa [Finset.mem_range] using hxmem
    have hxn : x < n := Nat.lt_of_lt_of_le hxk hk
    simp [hxk, hxn, Fin.castLE]
  rw [hsmall]
  symm
  apply Finset.sum_subset
    (by
      intro x hx
      have hxk : x < k := by
        simpa [Finset.mem_range] using hx
      simp [Finset.mem_range, Nat.lt_of_lt_of_le hxk hk])
    (by
      intro x hx_n hx_not_k
      have hxn : x < n := by
        simpa [Finset.mem_range] using hx_n
      have hxge : k ≤ x := by
        exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx_not_k)
      simp [hxn, hzero ⟨x, hxn⟩ hxge])

/-- **Theorem 9.1 / Problem 9.2 support**, leading-principal determinant
product for an exact LU certificate.  If a full exact `LUFactSpec` is already
available, then every leading principal block determinant is the product of the
corresponding leading pivots.  This is only the determinant side of Higham's
Theorem 9.1; the existence and uniqueness of the exact LU certificate from
nonzero leading principal minors remains a separate target. -/
theorem higham9_1_leadingPrincipalBlock_det_eq_pivot_product {n k : ℕ}
    (hk : k ≤ n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) =
      ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) := by
  classical
  let Aₖ : Fin k → Fin k → ℝ :=
    fun i j => A (Fin.castLE hk i) (Fin.castLE hk j)
  let Lₖ : Fin k → Fin k → ℝ :=
    fun i j => L (Fin.castLE hk i) (Fin.castLE hk j)
  let Uₖ : Fin k → Fin k → ℝ :=
    fun i j => U (Fin.castLE hk i) (Fin.castLE hk j)
  have hLUₖ : LUFactSpec k Aₖ Lₖ Uₖ := by
    refine
      { L_diag := ?_
        L_upper_zero := ?_
        U_lower_zero := ?_
        product_eq := ?_ }
    · intro i
      simp [Lₖ, hLU.L_diag]
    · intro i j hij
      exact hLU.L_upper_zero (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)
    · intro i j hij
      exact hLU.U_lower_zero (Fin.castLE hk i) (Fin.castLE hk j) (by simpa using hij)
    · intro i j
      have hsum :
          (∑ r : Fin n,
              L (Fin.castLE hk i) r * U r (Fin.castLE hk j)) =
            ∑ r : Fin k,
              L (Fin.castLE hk i) (Fin.castLE hk r) *
                U (Fin.castLE hk r) (Fin.castLE hk j) := by
        apply sum_fin_eq_sum_castLE_of_eq_zero hk
        intro r hr
        have hj_lt_r : (Fin.castLE hk j).val < r.val := by
          have hj_lt_k : j.val < k := j.isLt
          simpa using Nat.lt_of_lt_of_le hj_lt_k hr
        simp [hLU.U_lower_zero r (Fin.castLE hk j) hj_lt_r]
      have hprod := hLU.product_eq (Fin.castLE hk i) (Fin.castLE hk j)
      calc
        (∑ r : Fin k, Lₖ i r * Uₖ r j)
            = ∑ r : Fin k,
                L (Fin.castLE hk i) (Fin.castLE hk r) *
                  U (Fin.castLE hk r) (Fin.castLE hk j) := by
              simp [Lₖ, Uₖ]
        _ = ∑ r : Fin n,
              L (Fin.castLE hk i) r * U r (Fin.castLE hk j) := hsum.symm
        _ = A (Fin.castLE hk i) (Fin.castLE hk j) := hprod
        _ = Aₖ i j := by simp [Aₖ]
  simpa [Aₖ, Uₖ] using hLUₖ.det_eq_prod_U_diag

/-- **Theorem 9.1 / Problem 9.2 support**, nonzero leading determinant
consequence for an exact LU certificate: a leading principal block is
nonsingular exactly when its corresponding leading pivots are nonzero. -/
theorem higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero {n k : ℕ}
    (hk : k ≤ n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (fun i j : Fin k => A (Fin.castLE hk i) (Fin.castLE hk j)) ≠ 0 ↔
      ∀ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) ≠ 0 := by
  rw [higham9_1_leadingPrincipalBlock_det_eq_pivot_product hk hLU]
  simpa using
    (Finset.prod_ne_zero_iff :
      (∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i)) ≠ 0 ↔
        ∀ i ∈ (Finset.univ : Finset (Fin k)),
          U (Fin.castLE hk i) (Fin.castLE hk i) ≠ 0)

/-- **Algorithm 9.2**, dense square executable-loop certificate.  This records
that the stored factors come from the literal rounded Doolittle row and column
folds, together with the visible residual-compression budgets needed to produce
the compact `DoolittleLU` recurrence certificate. -/
abbrev higham9_2_DoolittleDenseLoopCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel) : Prop :=
  DoolittleDenseLoopCertificate n A L_hat U_hat fp

/-- **Algorithm 9.2**, dense square absolute-budget certificate.  This is the
implementation-facing layer immediately below
`higham9_2_DoolittleDenseLoopCertificate`: absolute residual budgets are kept
explicit until separate dominance hypotheses compress them to the relative
Doolittle recurrence budget. -/
abbrev higham9_2_DoolittleDenseLoopAbsBudgetCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel)
    (BU BL : Fin n → Fin n → ℝ) : Prop :=
  DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL

/-- **Algorithm 9.2**, dense-loop handoff: a literal dense Doolittle loop
certificate with visible compression budgets produces the compact source-facing
`DoolittleLU` certificate used by Theorem 9.3. -/
theorem higham9_2_denseLoopCertificate_to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L_hat U_hat fp :=
  DoolittleDenseLoopCertificate.to_DoolittleLU hC (gamma_nonneg fp hn)

/-- **Algorithm 9.2**, absolute-budget handoff: explicit upper/lower absolute
budgets plus their dominance proofs produce the compact source-facing
`DoolittleLU` certificate. -/
theorem higham9_2_absBudgetCertificate_to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    {BU BL : Fin n → Fin n → ℝ}
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L_hat U_hat fp :=
  DoolittleDenseLoopAbsBudgetCertificate.to_DoolittleLU hC (gamma_nonneg fp hn)

/-- **Theorem 9.3**, pivoted certificate form: if Gaussian elimination with
row pivoting has produced a backward-error certificate for `PA`, then the
standard `gamma_n` perturbation theorem applies to the row-permuted source
matrix.  This is a certificate adapter only; it does not construct the pivot
trace or prove that a particular loop produced the certificate. -/
theorem higham9_3_permuted_lu_backward_error_gamma {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU :
      higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n)) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  lu_backward_error_gamma fp n (higham9_2_rowPermutedMatrix A sigma)
    L_hat U_hat hn
    (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU)

/-- **Theorem 9.3 / equation (9.2a)**, exact row-pivoted `PA = LU`
certificates feed the standard `gamma_n` perturbation surface.  The exact
certificate supplies a zero residual and is weakened to `gamma_n` only to reuse
the common Theorem 9.3 API. -/
theorem higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L i k * U k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  higham9_3_permuted_lu_backward_error_gamma hn
    (higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma hn hLU)

/-- **Algorithm 9.2 / Theorem 9.3**, row-pivoted dense-loop handoff.

If the literal dense Doolittle loop certificate is proved for the row-permuted
matrix `PA`, then it supplies Higham's pivoted backward-error certificate
`L_hat U_hat = PA + ΔA`.  The row permutation remains an explicit hypothesis;
this adapter does not construct the pivoting trace. -/
theorem higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat fp) :
    higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) := by
  have hBE :
      LUBackwardError n (higham9_2_rowPermutedMatrix A sigma)
        L_hat U_hat (gamma fp n) :=
    DoolittleDenseLoopCertificate.to_LUBackwardError hC hn
  exact
    { perm := hsigma
      L_diag := hBE.L_diag
      L_upper_zero := hBE.L_upper_zero
      U_lower_zero := hBE.U_lower_zero
      backward_bound := by
        intro i j
        simpa [higham9_2_rowPermutedMatrix] using hBE.backward_bound i j }

/-- **Algorithm 9.2 / Theorem 9.3**, row-pivoted absolute-budget handoff.

Absolute residual budgets for a dense Doolittle run on `PA`, once compressed
by their visible dominance fields, produce the corresponding pivoted
backward-error certificate. -/
theorem higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat fp BU BL) :
    higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) := by
  have hBE :
      LUBackwardError n (higham9_2_rowPermutedMatrix A sigma)
        L_hat U_hat (gamma fp n) :=
    DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError hC hn
  exact
    { perm := hsigma
      L_diag := hBE.L_diag
      L_upper_zero := hBE.L_upper_zero
      U_lower_zero := hBE.U_lower_zero
      backward_bound := by
        intro i j
        simpa [higham9_2_rowPermutedMatrix] using hBE.backward_bound i j }

/-- **Equation (9.2b)**, source column-permuted matrix `AQ` represented by the
permutation map `tau`. -/
def higham9_2_colPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (tau : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => A i (tau j)

/-- **Equation (9.2b)**, source row-and-column permuted matrix `PAQ`. -/
def higham9_2_rowColPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix (higham9_2_colPermutedMatrix A tau) sigma

/-- **Equation (9.2b)**, column permutations preserve Higham's max-entry norm. -/
theorem higham9_2_colPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {tau : Fin n → Fin n}
    (htau : IsPermutation n tau) :
    maxEntryNorm hn (higham9_2_colPermutedMatrix A tau) = maxEntryNorm hn A := by
  classical
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham9_2_colPermutedMatrix A tau i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_colPermutedMatrix] using
      entry_le_maxEntryNorm hn A i (tau j)
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham9_2_colPermutedMatrix A tau)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have htau_symm : tau (eTau.symm j) = j := by
      change eTau (eTau.symm j) = j
      exact Equiv.apply_symm_apply eTau j
    simpa [higham9_2_colPermutedMatrix, htau_symm] using
      entry_le_maxEntryNorm hn (higham9_2_colPermutedMatrix A tau)
        i (eTau.symm j)

/-- **Equation (9.2b)**, column permutations preserve the matrix infinity norm. -/
theorem higham9_2_colPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {tau : Fin n → Fin n}
    (htau : IsPermutation n tau) :
    infNorm (higham9_2_colPermutedMatrix A tau) = infNorm A := by
  classical
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          (∑ j : Fin n, |higham9_2_colPermutedMatrix A tau i j|) =
            ∑ j : Fin n, |A i j| := by
        simpa [higham9_2_colPermutedMatrix, eTau] using
          (Equiv.sum_comp eTau (fun j : Fin n => |A i j|))
      rw [hrow]
      exact row_sum_le_infNorm A i
    · exact infNorm_nonneg A
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          (∑ j : Fin n, |higham9_2_colPermutedMatrix A tau i j|) =
            ∑ j : Fin n, |A i j| := by
        simpa [higham9_2_colPermutedMatrix, eTau] using
          (Equiv.sum_comp eTau (fun j : Fin n => |A i j|))
      rw [← hrow]
      exact row_sum_le_infNorm (higham9_2_colPermutedMatrix A tau) i
    · exact infNorm_nonneg (higham9_2_colPermutedMatrix A tau)

/-- **Equation (9.2b)**, row/column permutations preserve Higham's
max-entry norm. -/
theorem higham9_2_rowColPermutedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau) :
    maxEntryNorm hn (higham9_2_rowColPermutedMatrix A sigma tau) =
      maxEntryNorm hn A := by
  calc
    maxEntryNorm hn (higham9_2_rowColPermutedMatrix A sigma tau) =
        maxEntryNorm hn (higham9_2_colPermutedMatrix A tau) := by
          simpa [higham9_2_rowColPermutedMatrix] using
            higham9_2_rowPermutedMatrix_maxEntryNorm hn
              (higham9_2_colPermutedMatrix A tau) hsigma
    _ = maxEntryNorm hn A :=
        higham9_2_colPermutedMatrix_maxEntryNorm hn A htau

/-- **Equation (9.2b)**, row/column permutations preserve the matrix
infinity norm. -/
theorem higham9_2_rowColPermutedMatrix_infNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau) :
    infNorm (higham9_2_rowColPermutedMatrix A sigma tau) = infNorm A := by
  calc
    infNorm (higham9_2_rowColPermutedMatrix A sigma tau) =
        infNorm (higham9_2_colPermutedMatrix A tau) := by
          simpa [higham9_2_rowColPermutedMatrix] using
            higham9_2_rowPermutedMatrix_infNorm
              (higham9_2_colPermutedMatrix A tau) hsigma
    _ = infNorm A :=
        higham9_2_colPermutedMatrix_infNorm A htau

/-- **Equation (9.2b)**, row/column permutations preserve nonsingularity. -/
theorem higham9_2_rowColPermutedMatrix_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  let eSigma : Equiv.Perm (Fin n) := Equiv.ofBijective sigma hsigma
  let eTau : Equiv.Perm (Fin n) := Equiv.ofBijective tau htau
  let B : Fin n → Fin n → ℝ := higham9_2_colPermutedMatrix A tau
  have hB_det :
      Matrix.det (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hdet_eq :
        Matrix.det (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) =
          ((Equiv.Perm.sign eTau : ℤ) : ℝ) *
            Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
      have hperm :=
        Matrix.det_permute' eTau
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
      simpa [B, eTau, higham9_2_colPermutedMatrix, Matrix.of_apply] using hperm
    rw [hdet_eq]
    have hsign : ((Equiv.Perm.sign eTau : ℤ) : ℝ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign eTau) with hs | hs <;>
        simp [hs]
    exact mul_ne_zero hsign hdet
  have hdet_eq :
      Matrix.det
          (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
            Matrix (Fin n) (Fin n) ℝ) =
        ((Equiv.Perm.sign eSigma : ℤ) : ℝ) *
          Matrix.det (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) eSigma
        (Matrix.of B : Matrix (Fin n) (Fin n) ℝ)
    simpa [B, eSigma, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign eSigma : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign eSigma) with hs | hs <;>
      simp [hs]
  exact mul_ne_zero hsign hB_det

/-- **Equation (9.2b)**, the first-pivot row/column swaps preserve the
max-entry norm. -/
theorem higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) (r s : Fin (m + 1)) :
    maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s)) =
      maxEntryNorm (Nat.succ_pos m) A := by
  let hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.succ_pos m⟩⟩
  apply le_antisymm
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j =>
            |higham9_2_rowColPermutedMatrix A
              (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s) i j|)) ≤
      maxEntryNorm (Nat.succ_pos m) A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix] using
      entry_le_maxEntryNorm (Nat.succ_pos m) A
        (higham9_7_firstPivotRowSwap r i) (higham9_7_firstPivotRowSwap s j)
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hri :
        higham9_7_firstPivotRowSwap r (higham9_7_firstPivotRowSwap r i) = i :=
      higham9_7_firstPivotRowSwap_involutive r i
    have hsj :
        higham9_7_firstPivotRowSwap s (higham9_7_firstPivotRowSwap s j) = j :=
      higham9_7_firstPivotRowSwap_involutive s j
    simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix, hri, hsj] using
      entry_le_maxEntryNorm (Nat.succ_pos m)
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
        (higham9_7_firstPivotRowSwap r i) (higham9_7_firstPivotRowSwap s j)

/-- **Section 9.1 / complete-pivoting support**, after moving a first complete
pivot to `(0,0)`, row zero is a valid first-column partial pivot. -/
theorem higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) {r s : Fin (m + 1)}
    (hchoice : higham9_1_completePivotChoice A 0 r s) :
    higham9_1_partialPivotChoice
      (higham9_2_rowColPermutedMatrix A
        (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))
      0 0 := by
  refine ⟨le_rfl, ?_⟩
  intro i _hi
  simpa [higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
    higham9_2_colPermutedMatrix, higham9_7_firstPivotRowSwap] using
    hchoice.2.2 (higham9_7_firstPivotRowSwap r i) s
      (Nat.zero_le _) hchoice.2.1

/-- **Theorem 9.8 / complete-pivoting support**, the first complete-pivoting
Schur complement has max-entry norm at most twice the original max-entry norm. -/
theorem higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two {m : ℕ}
    (hm : 0 < m) (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {r s : Fin (m + 1)}
    (hchoice : higham9_1_completePivotChoice A 0 r s)
    (hpivot : A r s ≠ 0) :
    maxEntryNorm hm
        (luFirstSchurComplement
          (higham9_2_rowColPermutedMatrix A
            (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A
      (higham9_7_firstPivotRowSwap r) (higham9_7_firstPivotRowSwap s)
  have hpartial :
      higham9_1_partialPivotChoice B 0 0 := by
    simpa [B] using
      higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero A hchoice
  have hpivB : B 0 0 ≠ 0 := by
    simpa [B, higham9_2_rowColPermutedMatrix, higham9_2_rowPermutedMatrix,
      higham9_2_colPermutedMatrix, higham9_7_firstPivotRowSwap] using hpivot
  have hpartial_bound :=
    higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two
      hm B (0 : Fin (m + 1)) hpartial hpivB
  have hBmax :
      maxEntryNorm (Nat.succ_pos m) B = maxEntryNorm (Nat.succ_pos m) A := by
    simpa [B] using
      higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm A r s
  calc
    maxEntryNorm hm (luFirstSchurComplement B)
        ≤ 2 * maxEntryNorm (Nat.succ_pos m) B := by
          simpa [B, higham9_7_firstPivotRowSwap, higham9_2_rowPermutedMatrix] using
            hpartial_bound
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by rw [hBmax]

/-- **Equation (9.2b) / complete-pivoting first step**, row and column swaps
moving a chosen first complete pivot to `(0,0)` preserve nonsingularity. -/
theorem higham9_2_firstPivotRowColSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (r s : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham9_2_rowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  classical
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowPermutedMatrix A sigma
  have hB_det :
      Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
    simpa [B, sigma] using higham9_7_firstPivotRowSwap_det_ne_zero A r hdet
  let eTau : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective tau (higham9_7_firstPivotRowSwap_isPermutation s)
  have hdet_eq :
      Matrix.det
        (Matrix.of
          (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
        ((Equiv.Perm.sign eTau : ℤ) : ℝ) *
          Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    have hperm :=
      Matrix.det_permute' eTau
        (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    simpa [B, sigma, tau, eTau, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix, Matrix.of_apply]
      using hperm
  rw [hdet_eq]
  exact mul_ne_zero (by simp) hB_det

/-- **Equation (9.2b)**, source-facing exact complete-pivoting certificate
`PAQ = LU`, represented as a row-permuted LU certificate for `AQ` together
with an explicit column permutation condition. -/
abbrev higham9_2_CompletePermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n) : Prop :=
  IsPermutation n tau ∧
    PermutedLUFactSpec n (higham9_2_colPermutedMatrix A tau) L U sigma

/-- **Equation (9.2a)/(9.2b)**, a row-pivoted `PA = LU` certificate is a
complete-pivoting certificate with the identity column permutation. -/
theorem higham9_2_permutedLUFactSpec_to_CompletePermutedLUFactSpec_id {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hLU : higham9_2_PermutedLUFactSpec n A L U sigma) :
    higham9_2_CompletePermutedLUFactSpec n A L U sigma (fun j => j) := by
  refine ⟨?_, ?_⟩
  · show IsPermutation n (fun j : Fin n => j)
    exact Function.bijective_id
  · simpa [higham9_2_colPermutedMatrix] using hLU

/-- **Equation (9.2b)**, a source `PAQ = LU` certificate is an ordinary exact
LU certificate for the row-and-column permuted matrix. -/
theorem higham9_2_completePermutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    LUFactSpec n (higham9_2_rowColPermutedMatrix A sigma tau) L U := by
  simpa [higham9_2_rowColPermutedMatrix] using
    (higham9_2_permutedLUFactSpec_to_LUFactSpec hLU.2)

/-- **Equation (9.2b)**, determinant-pivot product for an explicit
complete-pivoting certificate `PAQ = LU`. -/
theorem higham9_2_completePermutedLUFactSpec_det_eq_pivot_product {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    Matrix.det
        (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i :=
  (higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU).det_eq_prod_U_diag

/-- **Equation (9.2b)**, nonsingularity consequence for an explicit
complete-pivoting certificate `PAQ = LU`. -/
theorem higham9_2_completePermutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    Matrix.det
        (Matrix.of (higham9_2_rowColPermutedMatrix A sigma tau) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 ↔
      ∀ i : Fin n, U i i ≠ 0 :=
  (higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU).det_ne_zero_iff_U_diag_ne_zero

/-- **Theorem 9.3 / equation (9.2b)**, source-facing complete-pivoting
backward-error certificate. -/
abbrev higham9_2_CompletePermutedLUBackwardError (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (ε : ℝ) : Prop :=
  IsPermutation n tau ∧
    PermutedLUBackwardError n (higham9_2_colPermutedMatrix A tau)
      L_hat U_hat sigma ε

/-- **Theorem 9.3 / equation (9.2b)**, a complete-pivoting backward-error
certificate is an ordinary LU backward-error certificate for `PAQ`. -/
theorem higham9_2_completePermutedLUBackwardError_to_LUBackwardError {n : ℕ}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    {ε : ℝ}
    (hLU :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau ε) :
    LUBackwardError n (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat ε := by
  simpa [higham9_2_rowColPermutedMatrix] using
    (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU.2)

/-- **Theorem 9.3 / equation (9.2b)**, exact complete-pivoted certificates
are zero-coefficient complete-pivoted backward-error certificates. -/
theorem higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_zero
    {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    higham9_2_CompletePermutedLUBackwardError n A L U sigma tau 0 :=
  ⟨hLU.1,
    higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero hLU.2⟩

/-- **Theorem 9.3 / equation (9.2b)**, exact complete-pivoted certificates can
be consumed at the standard `gamma_n` perturbation level.  This remains an
exact-factor adapter and does not construct a rounded complete-pivoting loop. -/
theorem higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    higham9_2_CompletePermutedLUBackwardError n A L U sigma tau
      (gamma fp n) :=
  ⟨hLU.1,
    higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma hn hLU.2⟩

/-- **Theorem 9.3**, complete-pivoting certificate form: if a backward-error
certificate is supplied for `PAQ`, then the standard `gamma_n` perturbation
theorem applies to the row-and-column permuted source matrix.  This is a
certificate adapter only; it does not construct the complete-pivoting trace. -/
theorem higham9_3_complete_permuted_lu_backward_error_gamma {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau (gamma fp n)) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  lu_backward_error_gamma fp n (higham9_2_rowColPermutedMatrix A sigma tau)
    L_hat U_hat hn
    (higham9_2_completePermutedLUBackwardError_to_LUBackwardError hLU)

/-- **Theorem 9.3 / equation (9.2b)**, exact complete-pivoted `PAQ = LU`
certificates feed the standard `gamma_n` perturbation surface. -/
theorem higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hn : gammaValid fp n)
    (hLU : higham9_2_CompletePermutedLUFactSpec n A L U sigma tau) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L i k * U k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  higham9_3_complete_permuted_lu_backward_error_gamma hn
    (higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma
      hn hLU)

/-- **Algorithm 9.2 / Theorem 9.3**, complete-pivoted dense-loop handoff.

If the literal dense Doolittle loop certificate is proved for the
row-and-column permuted matrix `PAQ`, then it supplies Higham's complete
pivoting backward-error certificate.  The row and column permutations remain
explicit; this is a certificate adapter, not a pivot-trace construction. -/
theorem higham9_2_completePermutedDenseLoopCertificate_to_CompletePermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n
      (higham9_2_rowColPermutedMatrix A sigma tau) L_hat U_hat fp) :
    higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n) := by
  refine ⟨htau, ?_⟩
  exact higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError
    (A := higham9_2_colPermutedMatrix A tau)
    (L_hat := L_hat) (U_hat := U_hat) (sigma := sigma)
    hsigma hn (by simpa [higham9_2_rowColPermutedMatrix] using hC)

/-- **Algorithm 9.2 / Theorem 9.3**, complete-pivoted absolute-budget handoff.

Absolute residual budgets for a dense Doolittle run on `PAQ`, once compressed
by their visible dominance fields, produce the corresponding complete-pivoting
backward-error certificate. -/
theorem higham9_2_completePermutedAbsBudgetCertificate_to_CompletePermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      (higham9_2_rowColPermutedMatrix A sigma tau) L_hat U_hat fp BU BL) :
    higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n) := by
  refine ⟨htau, ?_⟩
  exact higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError
    (A := higham9_2_colPermutedMatrix A tau)
    (L_hat := L_hat) (U_hat := U_hat) (sigma := sigma)
    (BU := BU) (BL := BL)
    hsigma hn (by simpa [higham9_2_rowColPermutedMatrix] using hC)

/-- **Equation (9.2b)**, right-inverse transport through row and column
permutations.

If `A_inv` is a visible right inverse of `A`, then the source `PAQ` matrix
`A(sigma i, tau j)` has right inverse `(i,j) ↦ A_inv(tau i, sigma j)`. -/
theorem higham9_2_rowColPermutedMatrix_right_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau)
    (hRight : IsRightInverse n A A_inv) :
    IsRightInverse n (higham9_2_rowColPermutedMatrix A sigma tau)
      (fun i j => A_inv (tau i) (sigma j)) := by
  classical
  intro i j
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  have hsum :
      (∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j)) =
        ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := by
    simpa [eTau] using
      (Equiv.sum_comp eTau
        (fun k : Fin n => A (sigma i) k * A_inv k (sigma j)))
  calc
    ∑ k : Fin n,
        higham9_2_rowColPermutedMatrix A sigma tau i k *
          (fun i j => A_inv (tau i) (sigma j)) k j
        = ∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j) := by
            simp [higham9_2_rowColPermutedMatrix,
              higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix]
    _ = ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := hsum
    _ = (if sigma i = sigma j then 1 else 0) := hRight (sigma i) (sigma j)
    _ = (if i = j then 1 else 0) := by
        by_cases hij : i = j
        · simp [hij]
        · have hsig_ne : sigma i ≠ sigma j := by
            intro hsig
            exact hij (hsigma.1 hsig)
          simp [hij, hsig_ne]

/-- **Algorithm 9.2**, literal floating-point upper-entry update. -/
noncomputable def higham9_2_flDoolittleUEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  flDoolittleUEntry fp n A L_hat U_hat k j

/-- **Algorithm 9.2**, literal floating-point lower-entry numerator update. -/
noncomputable def higham9_2_flDoolittleLNumerator (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  flDoolittleLNumerator fp n A L_hat U_hat i k

/-- **Algorithm 9.2**, literal floating-point lower-entry update. -/
noncomputable def higham9_2_flDoolittleLEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  flDoolittleLEntry fp n A L_hat U_hat i k

/-- **Algorithm 9.2**, literal source-budget handoff: the concrete upper and
lower absolute budgets produced by the rounded Doolittle folds, together with
visible dominance by the relative compression terms, produce the dense square
absolute-budget certificate used by the Chapter 9 Doolittle backward-error
surface. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUAbsBudget fp n A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLAbsBudget fp n A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_source_budgets
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, componentwise dominance handoff: work/product and
rounded-numerator dominance conditions imply the literal dense-Doolittle
absolute-budget certificate. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUWorkAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_work_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLWorkAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_prod_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_component_dominance
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_work_le hU_prod_le hL_work_le hL_prod_le hL_num_le

/-- **Algorithm 9.2**, exact-product no-cancellation handoff: exact-product
upper/lower margins, plus a lower rounded-numerator dominance condition,
produce the literal dense-Doolittle absolute-budget certificate. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_product_margins
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_margin hL_margin hL_num_le

/-- **Algorithm 9.2**, exact-product numerator-margin handoff: exact-product
work margins plus an explicit lower numerator margin produce the literal
dense-Doolittle absolute-budget certificate. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_margin : ∀ i k : Fin n, k.val < i.val →
      (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              doolittleLProductAbs fp n A L_hat U_hat i k) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_product_numerator_margins
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_margin hL_margin hL_num_margin

/-- **Algorithm 9.2**, exact-target gap handoff: source-visible gaps for the
literal rounded Doolittle upper and lower targets produce the dense square
absolute-budget certificate used by the Chapter 9 Doolittle backward-error
surface.  The gap hypotheses remain explicit; this theorem does not construct
the full rectangular executable trace. -/
theorem higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) := by
  exact
    DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_target_gaps
      hL_diag hL_upper_zero hU_lower_zero
      (by
        intro k j hkj
        simpa [higham9_2_flDoolittleUEntry] using hU_entry_eq k j hkj)
      (by
        intro i k hki
        simpa [higham9_2_flDoolittleLEntry] using hL_entry_eq i k hki)
      hU_diag hn hU_gap hL_gap hL_num_gap

/-- **Algorithm 9.2**, rectangular row embedding.  Under the source hypothesis
`m >= n`, the pivot row index `k : Fin n` is also a valid row index of the
rectangular `m x n` input. -/
def higham9_2_rectRow {m n : ℕ} (hmn : n ≤ m) (k : Fin n) : Fin m :=
  ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩

/-- **Algorithm 9.2**, rectangular exact prefix dot product appearing in
equations (9.3) and (9.4). -/
noncomputable def higham9_2_rectPrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin n, (if s.val < k.val then L i s * U s j else 0)

/-- **Algorithm 9.2**, exact rectangular upper-entry update for equation
(9.3). -/
noncomputable def higham9_2_rectDoolittleUUpdate {m n : ℕ} (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  A (higham9_2_rectRow hmn k) j -
    higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k

/-- **Algorithm 9.2**, exact rectangular lower-entry update for equation
(9.4). -/
noncomputable def higham9_2_rectDoolittleLUpdate {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  (A i k - higham9_2_rectPrefixDot L U i k k) / U k k

/-- **Algorithm 9.2**, literal floating-point rectangular upper-entry update.
This is the row-specialized rounded Doolittle fold for the source `m x n`
variant: the pivot row `k : Fin n` is embedded into the rectangular row index
using the source-side hypothesis `n <= m`. -/
noncomputable def higham9_2_rectFlDoolittleUEntry {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  flDoolittleUEntry fp n
    (fun _ j => A (higham9_2_rectRow hmn k) j)
    (fun _ s => L (higham9_2_rectRow hmn k) s)
    U k j

/-- **Algorithm 9.2**, literal floating-point rectangular lower-entry
numerator update before division by the computed pivot. -/
noncomputable def higham9_2_rectFlDoolittleLNumerator {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  flDoolittleLNumerator fp n
    (fun _ j => A i j)
    (fun _ s => L i s)
    U k k

/-- **Algorithm 9.2**, literal floating-point rectangular lower-entry update
after rounded division by the computed pivot. -/
noncomputable def higham9_2_rectFlDoolittleLEntry {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  fp.fl_div (higham9_2_rectFlDoolittleLNumerator fp A L U i k) (U k k)

/-- **Algorithm 9.2**, one rectangular rounded lower-factor stage update.

At stage `k`, the executable rectangular Doolittle loop writes only column
`k` of `L`: entries above the pivot row are zero, the pivot-row entry is one,
and entries below the pivot row are produced by the literal rounded lower
fold using the stage state after the current upper row, including the pivot,
has been written. -/
noncomputable def higham9_2_rectRoundedStageUpdateL {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) : Fin m → Fin n → ℝ :=
  fun i j =>
    if _hcol : j = k then
      if _hupper : i.val < k.val then
        0
      else if _hbelow : k.val < i.val then
        higham9_2_rectFlDoolittleLEntry fp A L U i k
      else
        1
    else
      L i j

/-- **Algorithm 9.2**, one rectangular rounded upper-factor stage update.

At stage `k`, the executable rectangular Doolittle loop writes only row `k`
of `U`: entries left of the pivot are zero and active row entries are produced
by the literal rounded upper fold using the incoming stage state. -/
noncomputable def higham9_2_rectRoundedStageUpdateU {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i j =>
    if _hrow : i = k then
      if _hleft : j.val < k.val then
        0
      else
        higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
    else
      U i j

/-- **Algorithm 9.2**, executable rectangular Doolittle stage state. -/
abbrev higham9_2_RectDoolittleRoundedState (m n : ℕ) :=
  (Fin m → Fin n → ℝ) × (Fin n → Fin n → ℝ)

/-- **Algorithm 9.2**, all-zero initial rectangular Doolittle state. -/
noncomputable def higham9_2_rectRoundedInitialState (m n : ℕ) :
    higham9_2_RectDoolittleRoundedState m n :=
  (fun _ _ => 0, fun _ _ => 0)

/-- **Algorithm 9.2**, one executable rectangular rounded Doolittle stage. -/
noncomputable def higham9_2_rectRoundedStageStep {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : Fin n)
    (state : higham9_2_RectDoolittleRoundedState m n) :
    higham9_2_RectDoolittleRoundedState m n :=
  let U₁ := higham9_2_rectRoundedStageUpdateU fp hmn A state.1 state.2 k
  (higham9_2_rectRoundedStageUpdateL fp A state.1 U₁ k, U₁)

/-- **Algorithm 9.2**, finite executable rectangular rounded Doolittle prefix.

`higham9_2_rectRoundedLoopState fp hmn A T hT` is the state after the first
`T` stages, starting from the zero rectangular factors. -/
noncomputable def higham9_2_rectRoundedLoopState {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    ∀ T : ℕ, T ≤ n → higham9_2_RectDoolittleRoundedState m n
  | 0, _ => higham9_2_rectRoundedInitialState m n
  | T + 1, hT =>
      let prev := higham9_2_rectRoundedLoopState fp hmn A T
        (Nat.le_of_succ_le hT)
      higham9_2_rectRoundedStageStep fp hmn A ⟨T, Nat.lt_of_succ_le hT⟩ prev

/-- **Algorithm 9.2**, executable rectangular rounded lower factor. -/
noncomputable def higham9_2_rectRoundedLoopL {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  (higham9_2_rectRoundedLoopState fp hmn A n (Nat.le_refl n)).1

/-- **Algorithm 9.2**, executable rectangular rounded upper factor. -/
noncomputable def higham9_2_rectRoundedLoopU {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  (higham9_2_rectRoundedLoopState fp hmn A n (Nat.le_refl n)).2

/-- **Algorithm 9.2**, local transition certificate for one executable
rectangular rounded Doolittle stage.  The upper-row fold is stated against the
incoming state, while the lower-column fold uses the just-updated upper row so
the division pivot is the computed `U k k`, as in Algorithm 9.2.  Later
preservation lemmas transport these local transition facts to the final
self-referential dense-loop trace. -/
structure higham9_2_RectDoolittleRoundedStageTransition {m n : ℕ}
    (hmn : n ≤ m) (A L₀ L₁ : Fin m → Fin n → ℝ)
    (U₀ U₁ : Fin n → Fin n → ℝ) (fp : FPModel) (k : Fin n) : Prop where
  /-- The stage writes the rectangular pivot-row diagonal entry of `L`. -/
  L_diag_stage : L₁ (higham9_2_rectRow hmn k) k = 1
  /-- The stage writes zeros above the rectangular pivot in column `k`. -/
  L_upper_zero_stage : ∀ i : Fin m, i.val < k.val → L₁ i k = 0
  /-- The stage writes zeros left of the pivot in row `k` of `U`. -/
  U_lower_zero_stage : ∀ j : Fin n, j.val < k.val → U₁ k j = 0
  /-- Active upper-row entries are the literal rounded folds from the incoming state. -/
  U_stage_eq_prev : ∀ j : Fin n, k.val ≤ j.val →
    U₁ k j = higham9_2_rectFlDoolittleUEntry fp hmn A L₀ U₀ k j
  /-- Active lower-column entries are the literal rounded folds after the
  current upper row, including the pivot, has been written. -/
  L_stage_eq_prev : ∀ i : Fin m, k.val < i.val →
    L₁ i k = higham9_2_rectFlDoolittleLEntry fp A L₀ U₁ i k
  /-- Non-stage lower-factor columns are preserved. -/
  L_preserve_off_stage : ∀ i : Fin m, ∀ j : Fin n, j ≠ k → L₁ i j = L₀ i j
  /-- Non-stage upper-factor rows are preserved. -/
  U_preserve_off_stage : ∀ i j : Fin n, i ≠ k → U₁ i j = U₀ i j

/-- **Algorithm 9.2**, the concrete rectangular stage update satisfies the
local rounded Doolittle transition certificate. -/
theorem higham9_2_rectRoundedStageTransition_of_update {m n : ℕ}
    {fp : FPModel} {hmn : n ≤ m}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) :
    higham9_2_RectDoolittleRoundedStageTransition hmn A L
      (higham9_2_rectRoundedStageUpdateL fp A L
        (higham9_2_rectRoundedStageUpdateU fp hmn A L U k) k)
      U
      (higham9_2_rectRoundedStageUpdateU fp hmn A L U k) fp k := by
  refine {
  L_diag_stage := by
    simp [higham9_2_rectRoundedStageUpdateL, higham9_2_rectRow]
  L_upper_zero_stage := by
    intro i hi
    simp [higham9_2_rectRoundedStageUpdateL, hi]
  U_lower_zero_stage := by
    intro j hj
    simp [higham9_2_rectRoundedStageUpdateU, hj]
  U_stage_eq_prev := by
    intro j hkj
    have hnot : ¬ j.val < k.val := Nat.not_lt_of_ge hkj
    simp [higham9_2_rectRoundedStageUpdateU, hnot]
  L_stage_eq_prev := by
    intro i hki
    have hnot : ¬ i.val < k.val := Nat.not_lt_of_ge (Nat.le_of_lt hki)
    simp [higham9_2_rectRoundedStageUpdateL, hnot, hki]
  L_preserve_off_stage := by
    intro i j hj
    simp [higham9_2_rectRoundedStageUpdateL, hj]
  U_preserve_off_stage := by
    intro i j hi
    simp [higham9_2_rectRoundedStageUpdateU, hi]
  }

/-- **Algorithm 9.2**, every successor loop prefix is produced by one
certificate-backed rectangular rounded Doolittle transition. -/
theorem higham9_2_rectRoundedLoopState_succ_transition {m n : ℕ}
    {fp : FPModel} {hmn : n ≤ m} (A : Fin m → Fin n → ℝ)
    {T : ℕ} (hT : T + 1 ≤ n) :
    let prev := higham9_2_rectRoundedLoopState fp hmn A T
      (Nat.le_of_succ_le hT)
    let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
    higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
      prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
  dsimp [higham9_2_rectRoundedLoopState, higham9_2_rectRoundedStageStep]
  exact higham9_2_rectRoundedStageTransition_of_update A _ _ _

/-- **Algorithm 9.2**, later rectangular rounded loop stages preserve a
previously written lower-factor column for one successor step. -/
theorem higham9_2_rectRoundedLoopState_succ_L_column_stable_of_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (i : Fin m) (k : Fin n) (hkT : k.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).1 i k =
      (higham9_2_rectRoundedLoopState fp hmn A T
        (Nat.le_of_succ_le hT)).1 i k := by
  let prev := higham9_2_rectRoundedLoopState fp hmn A T
    (Nat.le_of_succ_le hT)
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  have hne : k ≠ (⟨T, Nat.lt_of_succ_le hT⟩ : Fin n) := by
    intro hk
    have hkval : k.val = T := congrArg Fin.val hk
    omega
  simpa [prev, next] using htr.L_preserve_off_stage i k hne

/-- **Algorithm 9.2**, later rectangular rounded loop stages preserve a
previously written upper-factor row for one successor step. -/
theorem higham9_2_rectRoundedLoopState_succ_U_row_stable_of_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (k j : Fin n) (hkT : k.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).2 k j =
      (higham9_2_rectRoundedLoopState fp hmn A T
        (Nat.le_of_succ_le hT)).2 k j := by
  let prev := higham9_2_rectRoundedLoopState fp hmn A T
    (Nat.le_of_succ_le hT)
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  have hne : k ≠ (⟨T, Nat.lt_of_succ_le hT⟩ : Fin n) := by
    intro hk
    have hkval : k.val = T := congrArg Fin.val hk
    omega
  simpa [prev, next] using htr.U_preserve_off_stage k j hne

/-- **Algorithm 9.2**, the successor loop prefix writes the current
rectangular pivot-row diagonal entry of `L`. -/
theorem higham9_2_rectRoundedLoopState_succ_L_diag_stage
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n) :
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).1
        (higham9_2_rectRow hmn ⟨T, Nat.lt_of_succ_le hT⟩)
        ⟨T, Nat.lt_of_succ_le hT⟩ = 1 := by
  let prev := higham9_2_rectRoundedLoopState fp hmn A T
    (Nat.le_of_succ_le hT)
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  simpa [prev, next] using htr.L_diag_stage

/-- **Algorithm 9.2**, the successor loop prefix writes the current zero
pattern above the rectangular pivot in column `T`. -/
theorem higham9_2_rectRoundedLoopState_succ_L_upper_zero_stage
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (i : Fin m) (hiT : i.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).1 i
        ⟨T, Nat.lt_of_succ_le hT⟩ = 0 := by
  let prev := higham9_2_rectRoundedLoopState fp hmn A T
    (Nat.le_of_succ_le hT)
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  simpa [prev, next] using htr.L_upper_zero_stage i hiT

/-- **Algorithm 9.2**, the successor loop prefix writes the current zero
pattern left of the rectangular pivot in row `T` of `U`. -/
theorem higham9_2_rectRoundedLoopState_succ_U_lower_zero_stage
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (j : Fin n) (hjT : j.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).2
        ⟨T, Nat.lt_of_succ_le hT⟩ j = 0 := by
  let prev := higham9_2_rectRoundedLoopState fp hmn A T
    (Nat.le_of_succ_le hT)
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  simpa [prev, next] using htr.U_lower_zero_stage j hjT

/-- **Algorithm 9.2**, active entries in the successor loop prefix's current
upper row are produced by the literal rounded upper fold from the previous
state. -/
theorem higham9_2_rectRoundedLoopState_succ_U_stage_eq_prev
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (j : Fin n) (hTj : T ≤ j.val) :
    let prev := higham9_2_rectRoundedLoopState fp hmn A T
      (Nat.le_of_succ_le hT)
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).2
        ⟨T, Nat.lt_of_succ_le hT⟩ j =
      higham9_2_rectFlDoolittleUEntry fp hmn A prev.1 prev.2
        ⟨T, Nat.lt_of_succ_le hT⟩ j := by
  intro prev
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  simpa [next] using htr.U_stage_eq_prev j hTj

/-- **Algorithm 9.2**, active entries in the successor loop prefix's current
lower column are produced by the literal rounded lower fold from the previous
state. -/
theorem higham9_2_rectRoundedLoopState_succ_L_stage_eq_prev
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T + 1 ≤ n)
    (i : Fin m) (hTi : T < i.val) :
    let prev := higham9_2_rectRoundedLoopState fp hmn A T
      (Nat.le_of_succ_le hT)
    (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).1 i
        ⟨T, Nat.lt_of_succ_le hT⟩ =
      higham9_2_rectFlDoolittleLEntry fp A prev.1
        (higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT).2 i
        ⟨T, Nat.lt_of_succ_le hT⟩ := by
  intro prev
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have htr :
      higham9_2_RectDoolittleRoundedStageTransition hmn A prev.1 next.1
        prev.2 next.2 fp ⟨T, Nat.lt_of_succ_le hT⟩ := by
    simpa [prev, next] using
      (higham9_2_rectRoundedLoopState_succ_transition
        (fp := fp) (hmn := hmn) A hT)
  simpa [next] using htr.L_stage_eq_prev i hTi

/-- **Algorithm 9.2**, once a lower-factor column has been written, all later
rectangular rounded loop stages preserve that column. -/
theorem higham9_2_rectRoundedLoopState_add_L_column_stable_of_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {S D : ℕ} (hSD : S + D ≤ n)
    (i : Fin m) (k : Fin n) (hkS : k.val < S) :
    (higham9_2_rectRoundedLoopState fp hmn A (S + D) hSD).1 i k =
      (higham9_2_rectRoundedLoopState fp hmn A S
        (Nat.le_trans (Nat.le_add_right S D) hSD)).1 i k := by
  induction D with
  | zero =>
      simp
  | succ D ih =>
      have hprev : S + D ≤ n := Nat.le_trans (Nat.le_succ (S + D)) (by
        simpa [Nat.add_assoc] using hSD)
      have hstep :
          (higham9_2_rectRoundedLoopState fp hmn A (S + (D + 1)) hSD).1 i k =
            (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).1 i k := by
        simpa [Nat.add_assoc] using
          (higham9_2_rectRoundedLoopState_succ_L_column_stable_of_lt
            (fp := fp) (hmn := hmn) A
            (T := S + D)
            (hT := by simpa [Nat.add_assoc] using hSD)
            i k (by omega))
      have htail :
          (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).1 i k =
            (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S D) hprev)).1 i k :=
        ih hprev
      calc
        (higham9_2_rectRoundedLoopState fp hmn A (S + (D + 1)) hSD).1 i k
            = (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).1 i k :=
              hstep
        _ = (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S D) hprev)).1 i k := htail
        _ = (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S (D + 1)) hSD)).1 i k := by
              rfl

/-- **Algorithm 9.2**, once an upper-factor row has been written, all later
rectangular rounded loop stages preserve that row. -/
theorem higham9_2_rectRoundedLoopState_add_U_row_stable_of_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {S D : ℕ} (hSD : S + D ≤ n)
    (k j : Fin n) (hkS : k.val < S) :
    (higham9_2_rectRoundedLoopState fp hmn A (S + D) hSD).2 k j =
      (higham9_2_rectRoundedLoopState fp hmn A S
        (Nat.le_trans (Nat.le_add_right S D) hSD)).2 k j := by
  induction D with
  | zero =>
      simp
  | succ D ih =>
      have hprev : S + D ≤ n := Nat.le_trans (Nat.le_succ (S + D)) (by
        simpa [Nat.add_assoc] using hSD)
      have hstep :
          (higham9_2_rectRoundedLoopState fp hmn A (S + (D + 1)) hSD).2 k j =
            (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).2 k j := by
        simpa [Nat.add_assoc] using
          (higham9_2_rectRoundedLoopState_succ_U_row_stable_of_lt
            (fp := fp) (hmn := hmn) A
            (T := S + D)
            (hT := by simpa [Nat.add_assoc] using hSD)
            k j (by omega))
      have htail :
          (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).2 k j =
            (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S D) hprev)).2 k j :=
        ih hprev
      calc
        (higham9_2_rectRoundedLoopState fp hmn A (S + (D + 1)) hSD).2 k j
            = (higham9_2_rectRoundedLoopState fp hmn A (S + D) hprev).2 k j :=
              hstep
        _ = (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S D) hprev)).2 k j := htail
        _ = (higham9_2_rectRoundedLoopState fp hmn A S
              (Nat.le_trans (Nat.le_add_right S (D + 1)) hSD)).2 k j := by
              rfl

/-- **Algorithm 9.2**, the executable rectangular rounded loop produces a
unit diagonal on the rectangular pivot rows of its final lower factor. -/
theorem higham9_2_rectRoundedLoopL_diag {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : Fin n) :
    higham9_2_rectRoundedLoopL fp hmn A (higham9_2_rectRow hmn k) k = 1 := by
  let S : ℕ := k.val + 1
  let D : ℕ := n - S
  have hS : S ≤ n := by
    simp [S]
  have hSD : S + D ≤ n := by
    simp [S, D, Nat.add_sub_cancel' hS]
  have hstable :=
    higham9_2_rectRoundedLoopState_add_L_column_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := D) hSD
      (higham9_2_rectRow hmn k) k (by simp [S])
  have hstage :
      (higham9_2_rectRoundedLoopState fp hmn A S
        (Nat.le_trans (Nat.le_add_right S D) hSD)).1
          (higham9_2_rectRow hmn k) k = 1 := by
    simpa [S] using
      (higham9_2_rectRoundedLoopState_succ_L_diag_stage
        (fp := fp) (hmn := hmn) A
        (T := k.val)
        (hT := by simp))
  simpa [higham9_2_rectRoundedLoopL, S, D, Nat.add_sub_cancel' hS] using
    hstable.trans hstage

/-- **Algorithm 9.2**, the executable rectangular rounded loop produces the
lower-trapezoidal zero pattern in its final lower factor. -/
theorem higham9_2_rectRoundedLoopL_upper_zero {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (hij : i.val < j.val) :
    higham9_2_rectRoundedLoopL fp hmn A i j = 0 := by
  let S : ℕ := j.val + 1
  let D : ℕ := n - S
  have hS : S ≤ n := by
    simp [S]
  have hSD : S + D ≤ n := by
    simp [S, D, Nat.add_sub_cancel' hS]
  have hstable :=
    higham9_2_rectRoundedLoopState_add_L_column_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := D) hSD
      i j (by simp [S])
  have hstage :
      (higham9_2_rectRoundedLoopState fp hmn A S
        (Nat.le_trans (Nat.le_add_right S D) hSD)).1 i j = 0 := by
    simpa [S] using
      (higham9_2_rectRoundedLoopState_succ_L_upper_zero_stage
        (fp := fp) (hmn := hmn) A
        (T := j.val)
        (hT := by simp)
        i hij)
  simpa [higham9_2_rectRoundedLoopL, S, D, Nat.add_sub_cancel' hS] using
    hstable.trans hstage

/-- **Algorithm 9.2**, the executable rectangular rounded loop produces the
upper-triangular zero pattern in its final upper factor. -/
theorem higham9_2_rectRoundedLoopU_lower_zero {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i j : Fin n) (hji : j.val < i.val) :
    higham9_2_rectRoundedLoopU fp hmn A i j = 0 := by
  let S : ℕ := i.val + 1
  let D : ℕ := n - S
  have hS : S ≤ n := by
    simp [S]
  have hSD : S + D ≤ n := by
    simp [S, D, Nat.add_sub_cancel' hS]
  have hstable :=
    higham9_2_rectRoundedLoopState_add_U_row_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := D) hSD
      i j (by simp [S])
  have hstage :
      (higham9_2_rectRoundedLoopState fp hmn A S
        (Nat.le_trans (Nat.le_add_right S D) hSD)).2 i j = 0 := by
    simpa [S] using
      (higham9_2_rectRoundedLoopState_succ_U_lower_zero_stage
        (fp := fp) (hmn := hmn) A
        (T := i.val)
        (hT := by simp)
        j hji)
  simpa [higham9_2_rectRoundedLoopU, S, D, Nat.add_sub_cancel' hS] using
    hstable.trans hstage

/-- **Algorithm 9.2**, any rectangular rounded loop prefix already agrees
with the final lower factor on columns whose stages are complete. -/
theorem higham9_2_rectRoundedLoopState_L_eq_final_of_col_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T ≤ n)
    (i : Fin m) (k : Fin n) (hkT : k.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A T hT).1 i k =
      higham9_2_rectRoundedLoopL fp hmn A i k := by
  let S : ℕ := k.val + 1
  let DT : ℕ := T - S
  let DN : ℕ := n - S
  have hS_T : S ≤ T := by
    simp [S]
    omega
  have hS_n : S ≤ n := Nat.le_trans hS_T hT
  have hSDT : S + DT ≤ n := by
    simp [S, DT, Nat.add_sub_cancel' hS_T, hT]
  have hSDN : S + DN ≤ n := by
    simp [S, DN, Nat.add_sub_cancel' hS_n]
  have hstableT :=
    higham9_2_rectRoundedLoopState_add_L_column_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := DT) hSDT
      i k (by simp [S])
  have hstableN :=
    higham9_2_rectRoundedLoopState_add_L_column_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := DN) hSDN
      i k (by simp [S])
  calc
    (higham9_2_rectRoundedLoopState fp hmn A T hT).1 i k =
        (higham9_2_rectRoundedLoopState fp hmn A (S + DT) hSDT).1 i k := by
          simp [S, DT, Nat.add_sub_cancel' hS_T]
    _ = (higham9_2_rectRoundedLoopState fp hmn A S
          (Nat.le_trans (Nat.le_add_right S DT) hSDT)).1 i k := hstableT
    _ = (higham9_2_rectRoundedLoopState fp hmn A S
          (Nat.le_trans (Nat.le_add_right S DN) hSDN)).1 i k := by
          rfl
    _ = (higham9_2_rectRoundedLoopState fp hmn A (S + DN) hSDN).1 i k :=
          hstableN.symm
    _ = higham9_2_rectRoundedLoopL fp hmn A i k := by
          simp [higham9_2_rectRoundedLoopL, S, DN, Nat.add_sub_cancel' hS_n]

/-- **Algorithm 9.2**, any rectangular rounded loop prefix already agrees
with the final upper factor on rows whose stages are complete. -/
theorem higham9_2_rectRoundedLoopState_U_eq_final_of_row_lt
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) {T : ℕ} (hT : T ≤ n)
    (k j : Fin n) (hkT : k.val < T) :
    (higham9_2_rectRoundedLoopState fp hmn A T hT).2 k j =
      higham9_2_rectRoundedLoopU fp hmn A k j := by
  let S : ℕ := k.val + 1
  let DT : ℕ := T - S
  let DN : ℕ := n - S
  have hS_T : S ≤ T := by
    simp [S]
    omega
  have hS_n : S ≤ n := Nat.le_trans hS_T hT
  have hSDT : S + DT ≤ n := by
    simp [S, DT, Nat.add_sub_cancel' hS_T, hT]
  have hSDN : S + DN ≤ n := by
    simp [S, DN, Nat.add_sub_cancel' hS_n]
  have hstableT :=
    higham9_2_rectRoundedLoopState_add_U_row_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := DT) hSDT
      k j (by simp [S])
  have hstableN :=
    higham9_2_rectRoundedLoopState_add_U_row_stable_of_lt
      (fp := fp) (hmn := hmn) A (S := S) (D := DN) hSDN
      k j (by simp [S])
  calc
    (higham9_2_rectRoundedLoopState fp hmn A T hT).2 k j =
        (higham9_2_rectRoundedLoopState fp hmn A (S + DT) hSDT).2 k j := by
          simp [S, DT, Nat.add_sub_cancel' hS_T]
    _ = (higham9_2_rectRoundedLoopState fp hmn A S
          (Nat.le_trans (Nat.le_add_right S DT) hSDT)).2 k j := hstableT
    _ = (higham9_2_rectRoundedLoopState fp hmn A S
          (Nat.le_trans (Nat.le_add_right S DN) hSDN)).2 k j := by
          rfl
    _ = (higham9_2_rectRoundedLoopState fp hmn A (S + DN) hSDN).2 k j :=
          hstableN.symm
    _ = higham9_2_rectRoundedLoopU fp hmn A k j := by
          simp [higham9_2_rectRoundedLoopU, S, DN, Nat.add_sub_cancel' hS_n]

/-- Congruence for the finite left fold used by literal rounded Doolittle
entries. -/
private theorem higham9_2_fin_foldl_congr {α : Type*} (n : ℕ)
    (f g : α → Fin n → α) (a : α)
    (h : ∀ acc s, f acc s = g acc s) :
    Fin.foldl n f a = Fin.foldl n g a := by
  induction n generalizing a with
  | zero =>
      rw [Fin.foldl_zero, Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      have hfold := ih
        (fun acc s => f acc s.castSucc)
        (fun acc s => g acc s.castSucc)
        a (by intro acc s; exact h acc s.castSucc)
      rw [hfold]
      exact h _ (Fin.last n)

/-- **Algorithm 9.2**, the rectangular rounded upper fold depends only on prior
lower columns and prior upper rows. -/
theorem higham9_2_rectFlDoolittleUEntry_eq_of_prefix {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (L₀ L₁ : Fin m → Fin n → ℝ) (U₀ U₁ : Fin n → Fin n → ℝ)
    (k j : Fin n)
    (hL : ∀ s : Fin n, s.val < k.val →
      L₀ (higham9_2_rectRow hmn k) s = L₁ (higham9_2_rectRow hmn k) s)
    (hU : ∀ s : Fin n, s.val < k.val → U₀ s j = U₁ s j) :
    higham9_2_rectFlDoolittleUEntry fp hmn A L₀ U₀ k j =
      higham9_2_rectFlDoolittleUEntry fp hmn A L₁ U₁ k j := by
  unfold higham9_2_rectFlDoolittleUEntry flDoolittleUEntry
  apply higham9_2_fin_foldl_congr
  intro acc s
  simp [hL ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩ s.isLt,
    hU ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩ s.isLt]

/-- **Algorithm 9.2**, the rectangular rounded lower numerator fold depends only
on prior lower columns and prior upper rows. -/
theorem higham9_2_rectFlDoolittleLNumerator_eq_of_prefix {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (L₀ L₁ : Fin m → Fin n → ℝ) (U₀ U₁ : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hL : ∀ s : Fin n, s.val < k.val → L₀ i s = L₁ i s)
    (hU : ∀ s : Fin n, s.val < k.val → U₀ s k = U₁ s k) :
    higham9_2_rectFlDoolittleLNumerator fp A L₀ U₀ i k =
      higham9_2_rectFlDoolittleLNumerator fp A L₁ U₁ i k := by
  unfold higham9_2_rectFlDoolittleLNumerator flDoolittleLNumerator
  apply higham9_2_fin_foldl_congr
  intro acc s
  simp [hL ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩ s.isLt,
    hU ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩ s.isLt]

/-- **Algorithm 9.2**, the rectangular rounded lower entry depends only on prior
lower columns, prior upper rows, and the current computed pivot. -/
theorem higham9_2_rectFlDoolittleLEntry_eq_of_prefix {m n : ℕ}
    (fp : FPModel) (A : Fin m → Fin n → ℝ)
    (L₀ L₁ : Fin m → Fin n → ℝ) (U₀ U₁ : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hL : ∀ s : Fin n, s.val < k.val → L₀ i s = L₁ i s)
    (hU : ∀ s : Fin n, s.val < k.val → U₀ s k = U₁ s k)
    (hPivot : U₀ k k = U₁ k k) :
    higham9_2_rectFlDoolittleLEntry fp A L₀ U₀ i k =
      higham9_2_rectFlDoolittleLEntry fp A L₁ U₁ i k := by
  unfold higham9_2_rectFlDoolittleLEntry
  rw [higham9_2_rectFlDoolittleLNumerator_eq_of_prefix
    fp A L₀ L₁ U₀ U₁ i k hL hU, hPivot]

/-- **Algorithm 9.2**, active entries in the final executable upper factor are
the literal rounded rectangular upper folds over the final factors. -/
theorem higham9_2_rectRoundedLoopU_stage_eq {m n : ℕ}
    {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) (k j : Fin n) (hkj : k.val ≤ j.val) :
    higham9_2_rectRoundedLoopU fp hmn A k j =
      higham9_2_rectFlDoolittleUEntry fp hmn A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A) k j := by
  let T : ℕ := k.val
  have hT : T + 1 ≤ n := Nat.succ_le_of_lt (by simp [T])
  have hTprev : T ≤ n := Nat.le_of_succ_le hT
  let kk : Fin n := ⟨T, Nat.lt_of_succ_le hT⟩
  have hkk : kk = k := by
    apply Fin.ext
    simp [kk, T]
  let prev := higham9_2_rectRoundedLoopState fp hmn A T hTprev
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have hstage :
      next.2 kk j =
        higham9_2_rectFlDoolittleUEntry fp hmn A prev.1 prev.2 kk j := by
    simpa [prev, next, kk, T] using
      (higham9_2_rectRoundedLoopState_succ_U_stage_eq_prev
        (fp := fp) (hmn := hmn) A (T := T) hT j
        (by simpa [T] using hkj))
  have hnext_final :
      next.2 kk j = higham9_2_rectRoundedLoopU fp hmn A kk j := by
    simpa [next] using
      (higham9_2_rectRoundedLoopState_U_eq_final_of_row_lt
        (fp := fp) (hmn := hmn) A (T := T + 1) hT kk j
        (by simp [kk, T]))
  have hentry :
      higham9_2_rectFlDoolittleUEntry fp hmn A prev.1 prev.2 kk j =
        higham9_2_rectFlDoolittleUEntry fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) kk j := by
    apply higham9_2_rectFlDoolittleUEntry_eq_of_prefix
    · intro s hs
      simpa [prev] using
        (higham9_2_rectRoundedLoopState_L_eq_final_of_col_lt
          (fp := fp) (hmn := hmn) A (T := T) hTprev
          (higham9_2_rectRow hmn kk) s hs)
    · intro s hs
      simpa [prev] using
        (higham9_2_rectRoundedLoopState_U_eq_final_of_row_lt
          (fp := fp) (hmn := hmn) A (T := T) hTprev s j hs)
  calc
    higham9_2_rectRoundedLoopU fp hmn A k j =
        next.2 kk j := by
          simpa [hkk] using hnext_final.symm
    _ = higham9_2_rectFlDoolittleUEntry fp hmn A prev.1 prev.2 kk j :=
        hstage
    _ = higham9_2_rectFlDoolittleUEntry fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) kk j := hentry
    _ = higham9_2_rectFlDoolittleUEntry fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j := by
        simp [hkk]

/-- **Algorithm 9.2**, active entries in the final executable lower factor are
the literal rounded rectangular lower folds over the final factors. -/
theorem higham9_2_rectRoundedLoopL_stage_eq {m n : ℕ}
    {fp : FPModel} {hmn : n ≤ m}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (k : Fin n) (hki : k.val < i.val) :
    higham9_2_rectRoundedLoopL fp hmn A i k =
      higham9_2_rectFlDoolittleLEntry fp A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A) i k := by
  let T : ℕ := k.val
  have hT : T + 1 ≤ n := Nat.succ_le_of_lt (by simp [T])
  have hTprev : T ≤ n := Nat.le_of_succ_le hT
  let kk : Fin n := ⟨T, Nat.lt_of_succ_le hT⟩
  have hkk : kk = k := by
    apply Fin.ext
    simp [kk, T]
  let prev := higham9_2_rectRoundedLoopState fp hmn A T hTprev
  let next := higham9_2_rectRoundedLoopState fp hmn A (T + 1) hT
  have hstage :
      next.1 i kk =
        higham9_2_rectFlDoolittleLEntry fp A prev.1 next.2 i kk := by
    simpa [prev, next, kk, T] using
      (higham9_2_rectRoundedLoopState_succ_L_stage_eq_prev
        (fp := fp) (hmn := hmn) A (T := T) hT i
        (by simpa [T] using hki))
  have hnext_final :
      next.1 i kk = higham9_2_rectRoundedLoopL fp hmn A i kk := by
    simpa [next] using
      (higham9_2_rectRoundedLoopState_L_eq_final_of_col_lt
        (fp := fp) (hmn := hmn) A (T := T + 1) hT i kk
        (by simp [kk, T]))
  have hentry :
      higham9_2_rectFlDoolittleLEntry fp A prev.1 next.2 i kk =
        higham9_2_rectFlDoolittleLEntry fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i kk := by
    apply higham9_2_rectFlDoolittleLEntry_eq_of_prefix
    · intro s hs
      simpa [prev] using
        (higham9_2_rectRoundedLoopState_L_eq_final_of_col_lt
          (fp := fp) (hmn := hmn) A (T := T) hTprev i s hs)
    · intro s hs
      simpa [next] using
        (higham9_2_rectRoundedLoopState_U_eq_final_of_row_lt
          (fp := fp) (hmn := hmn) A (T := T + 1) hT s kk
          (by omega))
    · simpa [next] using
        (higham9_2_rectRoundedLoopState_U_eq_final_of_row_lt
          (fp := fp) (hmn := hmn) A (T := T + 1) hT kk kk
          (by simp [kk, T]))
  calc
    higham9_2_rectRoundedLoopL fp hmn A i k =
        next.1 i kk := by
          simpa [hkk] using hnext_final.symm
    _ = higham9_2_rectFlDoolittleLEntry fp A prev.1 next.2 i kk := hstage
    _ = higham9_2_rectFlDoolittleLEntry fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i kk := hentry
    _ = higham9_2_rectFlDoolittleLEntry fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k := by
        simp [hkk]

/-- Exact-product term in the rectangular upper literal Doolittle budget. -/
noncomputable def higham9_2_rectDoolittleUProductAbs {m n : ℕ}
    (_fp : FPModel) (hmn : n ≤ m)
    (_A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
      U ⟨s.val, by omega⟩ j|

/-- Absolute work term multiplying `gamma fp k` in the rectangular upper
literal Doolittle budget. -/
noncomputable def higham9_2_rectDoolittleUWorkAbs {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  |A (higham9_2_rectRow hmn k) j| +
    ∑ s : Fin k.val,
      |fp.fl_mul
        (L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩)
        (U ⟨s.val, by omega⟩ j)|

/-- Concrete rectangular upper-entry absolute budget supplied by the literal
rounded Doolittle fold analysis. -/
noncomputable def higham9_2_rectDoolittleUAbsBudget {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  gamma fp k.val *
    (|A (higham9_2_rectRow hmn k) j| +
      ∑ s : Fin k.val,
        |fp.fl_mul
          (L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ j)|) +
    fp.u * higham9_2_rectDoolittleUProductAbs fp hmn A L U k j

/-- Exact-product term in the rectangular lower literal Doolittle budget. -/
noncomputable def higham9_2_rectDoolittleLProductAbs {m n : ℕ}
    (_fp : FPModel)
    (_A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ k|

/-- Absolute work term multiplying `gamma fp k` in the rectangular lower
literal Doolittle budget. -/
noncomputable def higham9_2_rectDoolittleLWorkAbs {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  |A i k| +
    ∑ s : Fin k.val,
      |fp.fl_mul (L i ⟨s.val, by omega⟩)
        (U ⟨s.val, by omega⟩ k)|

/-- Absolute lower numerator term in the rectangular literal Doolittle
budget. -/
noncomputable def higham9_2_rectDoolittleLNumeratorAbs {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  |higham9_2_rectFlDoolittleLNumerator fp A L U i k|

/-- Concrete rectangular lower-entry absolute budget supplied by the literal
rounded Doolittle numerator fold, division, and computed-pivot analysis. -/
noncomputable def higham9_2_rectDoolittleLAbsBudget {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  (gamma fp k.val *
    (|A i k| +
      ∑ s : Fin k.val,
        |fp.fl_mul (L i ⟨s.val, by omega⟩)
          (U ⟨s.val, by omega⟩ k)|) +
    fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k) +
    fp.u * higham9_2_rectDoolittleLNumeratorAbs fp A L U i k

/-- Rectangular upper componentwise dominance handoff: the two visible
non-probability work terms dominate the concrete upper absolute budget by the
relative `gamma fp n` compression radius. -/
theorem higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {k j : Fin n} (hn : gammaValid fp n) (_hkj : k.val ≤ j.val)
    (hwork :
      higham9_2_rectDoolittleUWorkAbs fp hmn A L U k j ≤ |U k j|)
    (hprod :
      higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|) :
    higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
      gamma fp n * |U k j| := by
  have hk1_le : k.val + 1 ≤ n := by
    omega
  have hk_valid : gammaValid fp k.val :=
    gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
  have hk1_valid : gammaValid fp (k.val + 1) :=
    gammaValid_mono fp hk1_le hn
  have hgk_nonneg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk_valid
  have hscale_nonneg : 0 ≤ |U k j| := abs_nonneg _
  have hwork' :
      gamma fp k.val *
          higham9_2_rectDoolittleUWorkAbs fp hmn A L U k j ≤
        gamma fp k.val * |U k j| :=
    mul_le_mul_of_nonneg_left hwork hgk_nonneg
  have hprod' :
      fp.u * higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤
        fp.u * |U k j| :=
    mul_le_mul_of_nonneg_left hprod fp.u_nonneg
  have hbudget :
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
        (gamma fp k.val + fp.u) * |U k j| := by
    calc
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j
          = gamma fp k.val *
              higham9_2_rectDoolittleUWorkAbs fp hmn A L U k j +
            fp.u *
              higham9_2_rectDoolittleUProductAbs fp hmn A L U k j := by
              simp [higham9_2_rectDoolittleUAbsBudget,
                higham9_2_rectDoolittleUWorkAbs,
                higham9_2_rectDoolittleUProductAbs]
      _ ≤ gamma fp k.val * |U k j| + fp.u * |U k j| :=
            add_le_add hwork' hprod'
      _ = (gamma fp k.val + fp.u) * |U k j| := by ring
  have hcoef :
      gamma fp k.val + fp.u ≤ gamma fp n :=
    le_trans (gamma_add_u_le fp k.val hk1_valid)
      (gamma_mono fp hk1_le hn)
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcoef hscale_nonneg)

/-- Rectangular lower componentwise dominance handoff.  Unlike the square
lower case, rows below a rectangular last pivot do not imply `k + 2 <= n`, so
the coefficient domination needed to compress the three work terms is kept as
an explicit hypothesis. -/
theorem higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n} (_hki : k.val < i.val)
    (hcoef : gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hwork :
      higham9_2_rectDoolittleLWorkAbs fp A L U i k ≤
        |L i k * U k k|)
    (hprod :
      higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|)
    (hnum :
      higham9_2_rectDoolittleLNumeratorAbs fp A L U i k ≤
        |L i k * U k k|)
    (hk : gammaValid fp k.val) :
    higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
      gamma fp n * |L i k * U k k| := by
  have hgk_nonneg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk
  have hscale_nonneg : 0 ≤ |L i k * U k k| := abs_nonneg _
  have hwork' :
      gamma fp k.val *
          higham9_2_rectDoolittleLWorkAbs fp A L U i k ≤
        gamma fp k.val * |L i k * U k k| :=
    mul_le_mul_of_nonneg_left hwork hgk_nonneg
  have hprod' :
      fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        fp.u * |L i k * U k k| :=
    mul_le_mul_of_nonneg_left hprod fp.u_nonneg
  have hnum' :
      fp.u * higham9_2_rectDoolittleLNumeratorAbs fp A L U i k ≤
        fp.u * |L i k * U k k| :=
    mul_le_mul_of_nonneg_left hnum fp.u_nonneg
  have hbudget :
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        (gamma fp k.val + fp.u + fp.u) * |L i k * U k k| := by
    calc
      higham9_2_rectDoolittleLAbsBudget fp A L U i k
          = (gamma fp k.val *
              higham9_2_rectDoolittleLWorkAbs fp A L U i k +
            fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k) +
            fp.u * higham9_2_rectDoolittleLNumeratorAbs fp A L U i k := by
              simp [higham9_2_rectDoolittleLAbsBudget,
                higham9_2_rectDoolittleLWorkAbs,
                higham9_2_rectDoolittleLProductAbs,
                higham9_2_rectDoolittleLNumeratorAbs]
      _ ≤ (gamma fp k.val * |L i k * U k k| +
            fp.u * |L i k * U k k|) +
            fp.u * |L i k * U k k| :=
            add_le_add (add_le_add hwork' hprod') hnum'
      _ = (gamma fp k.val + fp.u + fp.u) * |L i k * U k k| := by
            ring
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcoef hscale_nonneg)

/-- A rectangular upper exact-product no-cancellation margin dominates the
rounded-product work term used by the literal Doolittle budget. -/
theorem higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hmargin :
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|) :
    higham9_2_rectDoolittleUWorkAbs fp hmn A L U k j ≤ |U k j| := by
  let Arow : Fin n → Fin n → ℝ :=
    fun _ j => A (higham9_2_rectRow hmn k) j
  let Lrow : Fin n → Fin n → ℝ :=
    fun _ s => L (higham9_2_rectRow hmn k) s
  have hmargin' :
      |Arow k j| + (1 + fp.u) *
          doolittleUProductAbs fp n Arow Lrow U k j ≤ |U k j| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleUProductAbs,
      doolittleUProductAbs] using hmargin
  have hraw :=
    doolittleUWorkAbs_le_of_exact_product_margin
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (k := k) (j := j) hmargin'
  simpa [Arow, Lrow, higham9_2_rectDoolittleUWorkAbs] using hraw

/-- The same rectangular upper exact-product margin also dominates the upper
exact-product term itself. -/
theorem higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hmargin :
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|) :
    higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j| := by
  let Arow : Fin n → Fin n → ℝ :=
    fun _ j => A (higham9_2_rectRow hmn k) j
  let Lrow : Fin n → Fin n → ℝ :=
    fun _ s => L (higham9_2_rectRow hmn k) s
  have hmargin' :
      |Arow k j| + (1 + fp.u) *
          doolittleUProductAbs fp n Arow Lrow U k j ≤ |U k j| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleUProductAbs,
      doolittleUProductAbs] using hmargin
  have hraw :=
    doolittleUProductAbs_le_of_exact_product_margin
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (k := k) (j := j) hmargin'
  simpa [Arow, Lrow, higham9_2_rectDoolittleUProductAbs,
    doolittleUProductAbs] using hraw

/-- A rectangular lower exact-product no-cancellation margin dominates the
rounded-product work term used by the literal Doolittle budget. -/
theorem higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n}
    (hmargin :
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|) :
    higham9_2_rectDoolittleLWorkAbs fp A L U i k ≤
      |L i k * U k k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hmargin' :
      |Arow k k| + (1 + fp.u) *
          doolittleLProductAbs fp n Arow Lrow U k k ≤
        |Lrow k k * U k k| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
      doolittleLProductAbs] using hmargin
  have hraw :=
    doolittleLWorkAbs_le_of_exact_product_margin
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (i := k) (k := k) hmargin'
  simpa [Arow, Lrow, higham9_2_rectDoolittleLWorkAbs] using hraw

/-- The same rectangular lower exact-product margin also dominates the lower
exact-product term itself. -/
theorem higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n}
    (hmargin :
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|) :
    higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
      |L i k * U k k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hmargin' :
      |Arow k k| + (1 + fp.u) *
          doolittleLProductAbs fp n Arow Lrow U k k ≤
        |Lrow k k * U k k| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
      doolittleLProductAbs] using hmargin
  have hraw :=
    doolittleLProductAbs_le_of_exact_product_margin
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (i := k) (k := k) hmargin'
  simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
    doolittleLProductAbs] using hraw

/-- A rectangular lower exact-product numerator margin dominates the rounded
lower numerator itself. -/
theorem higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n} (hk : gammaValid fp k.val)
    (hmargin :
      (|A i k| + higham9_2_rectDoolittleLProductAbs fp A L U i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              higham9_2_rectDoolittleLProductAbs fp A L U i k) +
          fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k) ≤
        |L i k * U k k|) :
    higham9_2_rectDoolittleLNumeratorAbs fp A L U i k ≤
      |L i k * U k k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hmargin' :
      (|Arow k k| + doolittleLProductAbs fp n Arow Lrow U k k) +
        (gamma fp k.val *
            (|Arow k k| + (1 + fp.u) *
              doolittleLProductAbs fp n Arow Lrow U k k) +
          fp.u * doolittleLProductAbs fp n Arow Lrow U k k) ≤
        |Lrow k k * U k k| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
      doolittleLProductAbs] using hmargin
  have hraw :=
    doolittleLNumeratorAbs_le_of_exact_product_numerator_margin
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (i := k) (k := k) hk hmargin'
  simpa [Arow, Lrow, higham9_2_rectDoolittleLNumeratorAbs,
    higham9_2_rectFlDoolittleLNumerator, flDoolittleLNumerator] using hraw

/-- Exact upper-entry target before floating-point subtraction in the
rectangular literal Doolittle row fold. -/
noncomputable def higham9_2_rectDoolittleUExactTarget {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  A (higham9_2_rectRow hmn k) j -
    ∑ s : Fin k.val,
      L (higham9_2_rectRow hmn k) ⟨s.val, by omega⟩ *
        U ⟨s.val, by omega⟩ j

/-- Exact lower numerator target before floating-point subtraction and
division in the rectangular literal Doolittle column fold. -/
noncomputable def higham9_2_rectDoolittleLExactTarget {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  A i k -
    ∑ s : Fin k.val,
      L i ⟨s.val, by omega⟩ *
        U ⟨s.val, by omega⟩ k

/-- Explicit exact-product residual budget for the rectangular upper exact
target after the literal rounded Doolittle row fold has computed the stored
upper entry. -/
noncomputable def higham9_2_rectDoolittleUExactTargetResidualBudget
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) : ℝ :=
  gamma fp k.val *
      (|A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
        higham9_2_rectDoolittleUProductAbs fp hmn A L U k j) +
    fp.u * higham9_2_rectDoolittleUProductAbs fp hmn A L U k j

/-- Explicit exact-product residual budget for the rectangular lower exact
target after the literal rounded Doolittle numerator fold. -/
noncomputable def higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
    {m n : ℕ} (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  gamma fp k.val *
      (|A i k| + (1 + fp.u) *
        higham9_2_rectDoolittleLProductAbs fp A L U i k) +
    fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k

/-- Explicit exact-product residual budget for the rectangular lower exact
target after the literal rounded numerator is divided by the computed pivot
and multiplied back by that pivot. -/
noncomputable def higham9_2_rectDoolittleLExactTargetEntryResidualBudget
    {m n : ℕ} (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget fp A L U i k +
    fp.u * |higham9_2_rectFlDoolittleLNumerator fp A L U i k|

/-- A source-facing rectangular exact-target gap for an upper entry yields the
exact-product no-cancellation margin against the stored upper entry. -/
theorem higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {k j : Fin n} (hk : gammaValid fp k.val)
    (hentry : U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hgap :
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp hmn A L U k j ≤
        |higham9_2_rectDoolittleUExactTarget hmn A L U k j|) :
    |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
        higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j| := by
  let Arow : Fin n → Fin n → ℝ :=
    fun _ j => A (higham9_2_rectRow hmn k) j
  let Lrow : Fin n → Fin n → ℝ :=
    fun _ s => L (higham9_2_rectRow hmn k) s
  have hentry' : U k j = flDoolittleUEntry fp n Arow Lrow U k j := by
    simpa [Arow, Lrow, higham9_2_rectFlDoolittleUEntry] using hentry
  have hgap' :
      |Arow k j| + (1 + fp.u) *
          doolittleUProductAbs fp n Arow Lrow U k j +
        doolittleUExactTargetResidualBudget fp n Arow Lrow U k j ≤
        |doolittleUExactTarget n Arow Lrow U k j| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleUProductAbs,
      higham9_2_rectDoolittleUExactTarget,
      higham9_2_rectDoolittleUExactTargetResidualBudget,
      doolittleUProductAbs, doolittleUExactTarget,
      doolittleUExactTargetResidualBudget] using hgap
  have hraw :=
    doolittleUExactProductMargin_of_exactTarget_gap
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (k := k) (j := j) hk hentry' hgap'
  simpa [Arow, Lrow, higham9_2_rectDoolittleUProductAbs,
    doolittleUProductAbs] using hraw

/-- A source-facing rectangular exact-target gap for a lower entry yields the
exact-product no-cancellation margin against the stored lower pivot product. -/
theorem higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n} (hk : gammaValid fp k.val)
    (hU : U k k ≠ 0)
    (hentry : L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hgap :
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp A L U i k ≤
        |higham9_2_rectDoolittleLExactTarget A L U i k|) :
    |A i k| + (1 + fp.u) *
        higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
      |L i k * U k k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hentry' : Lrow k k = flDoolittleLEntry fp n Arow Lrow U k k := by
    simpa [Arow, Lrow, higham9_2_rectFlDoolittleLEntry,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLEntry,
      flDoolittleLNumerator] using hentry
  have hgap' :
      |Arow k k| + (1 + fp.u) *
          doolittleLProductAbs fp n Arow Lrow U k k +
        doolittleLExactTargetEntryResidualBudget fp n Arow Lrow U k k ≤
        |doolittleLExactTarget n Arow Lrow U k k| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
      higham9_2_rectDoolittleLExactTarget,
      higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget,
      higham9_2_rectDoolittleLExactTargetEntryResidualBudget,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLNumerator,
      doolittleLProductAbs, doolittleLExactTarget,
      doolittleLExactTargetNumeratorResidualBudget,
      doolittleLExactTargetEntryResidualBudget] using hgap
  have hraw :=
    doolittleLExactProductMargin_of_exactTarget_gap
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (i := k) (k := k) hk hU hentry' hgap'
  simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
    doolittleLProductAbs] using hraw

/-- A stronger source-facing rectangular exact-target gap yields the lower
exact-product numerator margin needed to dominate the rounded numerator
itself. -/
theorem higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap
    {m n : ℕ} {fp : FPModel}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {i : Fin m} {k : Fin n} (hk : gammaValid fp k.val)
    (hU : U k k ≠ 0)
    (hentry : L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hgap :
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L U i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L U i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L U i k ≤
        |higham9_2_rectDoolittleLExactTarget A L U i k|) :
    (|A i k| + higham9_2_rectDoolittleLProductAbs fp A L U i k) +
      higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
        fp A L U i k ≤
      |L i k * U k k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hentry' : Lrow k k = flDoolittleLEntry fp n Arow Lrow U k k := by
    simpa [Arow, Lrow, higham9_2_rectFlDoolittleLEntry,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLEntry,
      flDoolittleLNumerator] using hentry
  have hgap' :
      ((|Arow k k| + doolittleLProductAbs fp n Arow Lrow U k k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n Arow Lrow U k k) +
        doolittleLExactTargetEntryResidualBudget
          fp n Arow Lrow U k k ≤
        |doolittleLExactTarget n Arow Lrow U k k| := by
    simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
      higham9_2_rectDoolittleLExactTarget,
      higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget,
      higham9_2_rectDoolittleLExactTargetEntryResidualBudget,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLNumerator,
      doolittleLProductAbs, doolittleLExactTarget,
      doolittleLExactTargetNumeratorResidualBudget,
      doolittleLExactTargetEntryResidualBudget] using hgap
  have hraw :=
    doolittleLExactProductNumeratorMargin_of_exactTarget_gap
      (n := n) (fp := fp) (A := Arow) (L_hat := Lrow)
      (U_hat := U) (i := k) (k := k) hk hU hentry' hgap'
  simpa [Arow, Lrow, higham9_2_rectDoolittleLProductAbs,
    higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget,
    doolittleLProductAbs, doolittleLExactTargetNumeratorResidualBudget]
    using hraw

/-- **Algorithm 9.2**, rectangular rounded upper-entry residual.  The literal
rounded rectangular upper fold is within the explicit exact-product budget of
the exact equation (9.3) target. -/
theorem higham9_2_rectFlDoolittleUEntry_residual_abs_le {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) (hk : gammaValid fp k.val) :
    |higham9_2_rectDoolittleUUpdate hmn A L U k j -
      higham9_2_rectFlDoolittleUEntry fp hmn A L U k j| ≤
        higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j := by
  let Arow : Fin n → Fin n → ℝ :=
    fun _ j => A (higham9_2_rectRow hmn k) j
  let Lrow : Fin n → Fin n → ℝ :=
    fun _ s => L (higham9_2_rectRow hmn k) s
  have hraw :=
    flDoolittleUEntry_masked_exact_product_residual_abs_le
      fp n Arow Lrow U k j hk
  simpa [Arow, Lrow, higham9_2_rectDoolittleUUpdate,
    higham9_2_rectPrefixDot, higham9_2_rectFlDoolittleUEntry,
    higham9_2_rectDoolittleUAbsBudget,
    higham9_2_rectDoolittleUProductAbs] using hraw

/-- **Algorithm 9.2**, rectangular rounded lower numerator residual.  This is
the exact-product residual before the final rounded division by the computed
pivot. -/
theorem higham9_2_rectFlDoolittleLNumerator_residual_abs_le {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) (hk : gammaValid fp k.val) :
    |(A i k - higham9_2_rectPrefixDot L U i k k) -
      higham9_2_rectFlDoolittleLNumerator fp A L U i k| ≤
        gamma fp k.val *
          (|A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L i ⟨s.val, by omega⟩)
                (U ⟨s.val, by omega⟩ k)|) +
          fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hraw :=
    flDoolittleLNumerator_masked_exact_product_residual_abs_le
      fp n Arow Lrow U k k hk
  simpa [Arow, Lrow, higham9_2_rectPrefixDot,
    higham9_2_rectFlDoolittleLNumerator,
    higham9_2_rectDoolittleLProductAbs] using hraw

/-- **Algorithm 9.2**, rectangular rounded lower-entry pivot residual.  The
rounded division by the computed pivot gives an explicit residual once the
entry is multiplied back by that pivot. -/
theorem higham9_2_rectFlDoolittleLEntry_mul_pivot_sub_numerator_abs_le
    {m n : ℕ} (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) (hUkk : U k k ≠ 0) :
    |higham9_2_rectFlDoolittleLNumerator fp A L U i k -
      higham9_2_rectFlDoolittleLEntry fp A L U i k * U k k| ≤
        fp.u * |higham9_2_rectFlDoolittleLNumerator fp A L U i k| := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hraw :=
    flDoolittleLEntry_mul_pivot_sub_numerator_abs_le
      fp n Arow Lrow U k k hUkk
  simpa [Arow, Lrow, higham9_2_rectFlDoolittleLNumerator,
    higham9_2_rectFlDoolittleLEntry, flDoolittleLEntry] using hraw

/-- **Algorithm 9.2**, rectangular rounded lower-entry residual.  If the
stored lower entry is produced by the literal rounded rectangular update, then
equation (9.4)'s exact numerator target is within the explicit rectangular
absolute budget after multiplying by the computed pivot. -/
theorem higham9_2_rectFlDoolittleLEntry_residual_abs_le {m n : ℕ}
    (fp : FPModel)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hk : gammaValid fp k.val) (hUkk : U k k ≠ 0)
    (hentry : L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k) :
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
        higham9_2_rectDoolittleLAbsBudget fp A L U i k := by
  let Arow : Fin n → Fin n → ℝ := fun _ j => A i j
  let Lrow : Fin n → Fin n → ℝ := fun _ s => L i s
  have hentry_row :
      Lrow k k = flDoolittleLEntry fp n Arow Lrow U k k := by
    simpa [Arow, Lrow, higham9_2_rectFlDoolittleLEntry,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLEntry] using hentry
  have hraw :=
    flDoolittleLEntry_masked_exact_product_residual_abs_le
      fp n Arow Lrow U k k hk hUkk hentry_row
  simpa [Arow, Lrow, higham9_2_rectPrefixDot,
    higham9_2_rectFlDoolittleLNumerator,
    higham9_2_rectDoolittleLAbsBudget,
    higham9_2_rectDoolittleLProductAbs,
    higham9_2_rectDoolittleLNumeratorAbs] using hraw

/-- **Algorithm 9.2**, rectangular dense-loop certificate.  This is the
`m x n`, `m >= n` counterpart of the square dense-loop Doolittle certificate:
literal rounded rectangular entries are paired with visible relative residual
compression hypotheses.  It is an intermediate certificate surface, not a
complete executable loop schedule. -/
structure higham9_2_RectDoolittleDenseLoopCertificate {m n : ℕ}
    (hmn : n ≤ m) (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (fp : FPModel) : Prop where
  /-- The rectangular pivot rows of `L` have unit diagonal entries. -/
  L_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1
  /-- `L` is lower trapezoidal in the source rectangular sense. -/
  L_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0
  /-- `U` is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  /-- Upper entries agree with the literal rounded rectangular row fold. -/
  U_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
  /-- Lower entries agree with the literal rounded rectangular numerator fold
  followed by rounded division by the computed pivot. -/
  L_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k
  /-- Visible compression budget for rectangular upper entries. -/
  U_residual_compression : ∀ k j : Fin n, k.val ≤ j.val →
    |(A (higham9_2_rectRow hmn k) j -
      higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k) -
        U k j| ≤ gamma fp n * |U k j|
  /-- Visible compression budget for rectangular lower entries after
  multiplication by the computed pivot. -/
  L_residual_compression : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
      gamma fp n * |L i k * U k k|

/-- **Algorithm 9.2**, rectangular dense-loop absolute-budget certificate.
This layer records absolute residual budgets for the literal rounded
rectangular folds before they are compressed into the relative certificate. -/
structure higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate {m n : ℕ}
    (hmn : n ≤ m) (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (fp : FPModel) (BU : Fin n → Fin n → ℝ) (BL : Fin m → Fin n → ℝ) :
    Prop where
  /-- The rectangular pivot rows of `L` have unit diagonal entries. -/
  L_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1
  /-- `L` is lower trapezoidal in the source rectangular sense. -/
  L_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0
  /-- `U` is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  /-- Upper entries agree with the literal rounded rectangular row fold. -/
  U_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
  /-- Lower entries agree with the literal rounded rectangular numerator fold
  followed by rounded division by the computed pivot. -/
  L_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k
  /-- Absolute residual budget for rectangular upper entries. -/
  U_abs_residual : ∀ k j : Fin n, k.val ≤ j.val →
    |(A (higham9_2_rectRow hmn k) j -
      higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k) -
        U k j| ≤ BU k j
  /-- Dominance turning the upper absolute budget into the relative
  compression budget. -/
  U_budget_le_compression : ∀ k j : Fin n, k.val ≤ j.val →
    BU k j ≤ gamma fp n * |U k j|
  /-- Absolute residual budget for rectangular lower entries after
  multiplication by the computed pivot. -/
  L_abs_residual : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    |(A i k - higham9_2_rectPrefixDot L U i k k) - L i k * U k k| ≤
      BL i k
  /-- Dominance turning the lower absolute budget into the relative
  compression budget. -/
  L_budget_le_compression : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    BL i k ≤ gamma fp n * |L i k * U k k|

/-- **Algorithm 9.2**, rectangular rounded-stage trace.

This packages the ordered rectangular Doolittle loop surface before residual
compression: at each pivot stage `k`, the scheduled upper-row entries and
lower-column entries agree with the literal rounded folds for the current
stored factors.  Separate budget and nonbreakdown hypotheses are still needed
to turn this trace into the dense-loop certificate consumed by Theorem 9.3. -/
structure higham9_2_RectDoolittleRoundedStageTrace {m n : ℕ}
    (hmn : n ≤ m) (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (fp : FPModel) : Prop where
  /-- The rectangular pivot rows of `L` have unit diagonal entries. -/
  L_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1
  /-- `L` is lower trapezoidal in the source rectangular sense. -/
  L_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0
  /-- `U` is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  /-- Scheduled upper-row entries agree with the literal rounded row fold. -/
  U_stage_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
  /-- Scheduled lower-column entries agree with the literal rounded numerator
  fold followed by rounded division by the computed pivot. -/
  L_stage_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
    L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k

/-- **Algorithm 9.2**, rectangular rounded prefix trace.

After `t` scheduled Doolittle stages, all pivot rows/columns with index
strictly below `t` satisfy the corresponding triangular-shape and literal
rounded-fold equations.  The complete prefix `t = n` is converted below into
`higham9_2_RectDoolittleRoundedStageTrace`. -/
structure higham9_2_RectDoolittleRoundedPrefixTrace {m n : ℕ}
    (hmn : n ≤ m) (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (fp : FPModel) (t : ℕ) : Prop where
  /-- Completed pivot rows have unit diagonal entries. -/
  L_diag_done : ∀ k : Fin n, k.val < t →
    L (higham9_2_rectRow hmn k) k = 1
  /-- Completed lower-factor columns have the lower-trapezoidal zero pattern. -/
  L_upper_zero_done : ∀ i : Fin m, ∀ j : Fin n,
    j.val < t → i.val < j.val → L i j = 0
  /-- Completed upper-factor rows have the upper-triangular zero pattern. -/
  U_lower_zero_done : ∀ i j : Fin n,
    i.val < t → j.val < i.val → U i j = 0
  /-- Completed upper-row entries agree with the literal rounded row fold. -/
  U_stage_eq_done : ∀ k j : Fin n, k.val < t → k.val ≤ j.val →
    U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j
  /-- Completed lower-column entries agree with the literal rounded numerator
  fold followed by rounded division by the computed pivot. -/
  L_stage_eq_done : ∀ i : Fin m, ∀ k : Fin n,
    k.val < t → k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k

/-- **Algorithm 9.2**, the final executable rectangular rounded Doolittle loop
produces the rounded-stage trace expected by the certificate layer. -/
theorem higham9_2_rectRoundedLoopStageTrace {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    higham9_2_RectDoolittleRoundedStageTrace hmn A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) fp where
  L_diag := higham9_2_rectRoundedLoopL_diag fp hmn A
  L_upper_zero := higham9_2_rectRoundedLoopL_upper_zero fp hmn A
  U_lower_zero := higham9_2_rectRoundedLoopU_lower_zero fp hmn A
  U_stage_eq := higham9_2_rectRoundedLoopU_stage_eq A
  L_stage_eq := higham9_2_rectRoundedLoopL_stage_eq A

/-- **Algorithm 9.2**, rectangular absolute-budget handoff.  Absolute residual
budgets plus visible dominance inequalities produce the relative rectangular
dense-loop certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {BU : Fin n → Fin n → ℝ} {BL : Fin m → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L U fp BU BL) :
    higham9_2_RectDoolittleDenseLoopCertificate hmn A L U fp where
  L_diag := hC.L_diag
  L_upper_zero := hC.L_upper_zero
  U_lower_zero := hC.U_lower_zero
  U_entry_eq := hC.U_entry_eq
  L_entry_eq := hC.L_entry_eq
  U_residual_compression := by
    intro k j hkj
    exact le_trans (hC.U_abs_residual k j hkj)
      (hC.U_budget_le_compression k j hkj)
  L_residual_compression := by
    intro i k hki
    exact le_trans (hC.L_abs_residual i k hki)
      (hC.L_budget_le_compression i k hki)

/-- **Algorithm 9.2**, rectangular literal source-budget constructor.
Literal rounded rectangular Doolittle entries plus explicit budget dominance
produce the rectangular absolute-budget certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
        gamma fp n * |U k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) where
  L_diag := hL_diag
  L_upper_zero := hL_upper_zero
  U_lower_zero := hU_lower_zero
  U_entry_eq := hU_entry_eq
  L_entry_eq := hL_entry_eq
  U_abs_residual := by
    intro k j hkj
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    have hres :=
      higham9_2_rectFlDoolittleUEntry_residual_abs_le
        fp hmn A L U k j hk
    simpa [hU_entry_eq k j hkj] using hres
  U_budget_le_compression := hU_budget_le
  L_abs_residual := by
    intro i k hki
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    exact
      higham9_2_rectFlDoolittleLEntry_residual_abs_le
        fp A L U i k hk (hU_diag k) (hL_entry_eq i k hki)
  L_budget_le_compression := hL_budget_le

/-- **Algorithm 9.2**, rectangular rounded-stage trace to absolute-budget
certificate.  A scheduled rounded rectangular Doolittle trace, together with
nonzero computed pivots and visible budget dominance, produces the existing
absolute-budget certificate layer. -/
theorem higham9_2_rectRoundedStageTrace_to_rectAbsBudgetCertificate
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedStageTrace hmn A L U fp)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
        gamma fp n * |U k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) :=
  higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets
    hT.L_diag hT.L_upper_zero hT.U_lower_zero hT.U_stage_eq hT.L_stage_eq
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, rectangular rounded-stage trace to dense-loop
certificate.  This is the relative-compression handoff for a scheduled
rectangular rounded Doolittle trace. -/
theorem higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedStageTrace hmn A L U fp)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
        gamma fp n * |U k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopCertificate hmn A L U fp :=
  higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate
    (higham9_2_rectRoundedStageTrace_to_rectAbsBudgetCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Algorithm 9.2**, executable rectangular rounded loop to absolute-budget
certificate.  The concrete loop supplies the rounded-stage trace; callers still
provide the standard nonzero-pivot and budget-dominance hypotheses. -/
theorem higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp hmn A i k *
            higham9_2_rectRoundedLoopU fp hmn A k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A))
      (higham9_2_rectDoolittleLAbsBudget fp A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A)) :=
  higham9_2_rectRoundedStageTrace_to_rectAbsBudgetCertificate
    (higham9_2_rectRoundedLoopStageTrace fp hmn A)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, executable rectangular rounded loop to dense-loop
certificate under explicit nonzero-pivot and budget-dominance hypotheses. -/
theorem higham9_2_rectRoundedLoop_to_rectDenseLoopCertificate {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp hmn A i k *
            higham9_2_rectRoundedLoopU fp hmn A k k|) :
    higham9_2_RectDoolittleDenseLoopCertificate hmn A
      (higham9_2_rectRoundedLoopL fp hmn A)
      (higham9_2_rectRoundedLoopU fp hmn A) fp :=
  higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
    (higham9_2_rectRoundedLoopStageTrace fp hmn A)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, any full rounded-stage trace restricts to a completed
prefix trace after `t` rectangular Doolittle stages. -/
theorem higham9_2_rectRoundedStageTrace_to_prefixTrace
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedStageTrace hmn A L U fp)
    (t : ℕ) :
    higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp t where
  L_diag_done := by
    intro k _hk
    exact hT.L_diag k
  L_upper_zero_done := by
    intro i j _hj hij
    exact hT.L_upper_zero i j hij
  U_lower_zero_done := by
    intro i j _hi hji
    exact hT.U_lower_zero i j hji
  U_stage_eq_done := by
    intro k j _hk hkj
    exact hT.U_stage_eq k j hkj
  L_stage_eq_done := by
    intro i k _hk hki
    exact hT.L_stage_eq i k hki

/-- **Algorithm 9.2**, completed rectangular rounded prefix trace.  Once the
prefix horizon reaches all `n` stages, the prefix trace is exactly the rounded
stage trace consumed by the certificate and backward-error handoffs. -/
theorem higham9_2_rectRoundedPrefixTrace_complete_to_stageTrace
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp n) :
    higham9_2_RectDoolittleRoundedStageTrace hmn A L U fp where
  L_diag := by
    intro k
    exact hT.L_diag_done k k.isLt
  L_upper_zero := by
    intro i j hij
    exact hT.L_upper_zero_done i j j.isLt hij
  U_lower_zero := by
    intro i j hji
    exact hT.U_lower_zero_done i j i.isLt hji
  U_stage_eq := by
    intro k j hkj
    exact hT.U_stage_eq_done k j k.isLt hkj
  L_stage_eq := by
    intro i k hki
    exact hT.L_stage_eq_done i k k.isLt hki

/-- **Algorithm 9.2**, empty rectangular rounded prefix trace.  Before the
first Doolittle stage, no pivot row or column has been completed. -/
theorem higham9_2_rectRoundedPrefixTrace_zero
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ} :
    higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp 0 where
  L_diag_done := by
    intro k hk
    exact (Nat.not_lt_zero k.val hk).elim
  L_upper_zero_done := by
    intro i j hj _
    exact (Nat.not_lt_zero j.val hj).elim
  U_lower_zero_done := by
    intro i j hi _
    exact (Nat.not_lt_zero i.val hi).elim
  U_stage_eq_done := by
    intro k j hk _
    exact (Nat.not_lt_zero k.val hk).elim
  L_stage_eq_done := by
    intro i k hk _
    exact (Nat.not_lt_zero k.val hk).elim

/-- **Algorithm 9.2**, rectangular rounded prefix trace successor step.  A
completed prefix through stage `t`, plus the scheduled diagonal, triangular
shape, upper-row fold, and lower-column fold data for stage `t`, extends the
prefix to `t + 1`. -/
theorem higham9_2_rectRoundedPrefixTrace_succ
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {t : ℕ} (ht : t < n)
    (hprev : higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp t)
    (hL_diag :
      L (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ i : Fin m, i.val < t →
      L i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ j : Fin n, j.val < t →
      U ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ j : Fin n, t ≤ j.val →
      U ⟨t, ht⟩ j =
        higham9_2_rectFlDoolittleUEntry fp hmn A L U ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ i : Fin m, t < i.val →
      L i ⟨t, ht⟩ =
        higham9_2_rectFlDoolittleLEntry fp A L U i ⟨t, ht⟩) :
    higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp (t + 1) where
  L_diag_done := by
    intro k hk
    have hle : k.val ≤ t := Nat.lt_succ_iff.mp hk
    by_cases hkt : k.val < t
    · exact hprev.L_diag_done k hkt
    · have hkval : k.val = t := le_antisymm hle (Nat.le_of_not_gt hkt)
      have hk_eq : k = (⟨t, ht⟩ : Fin n) := Fin.ext hkval
      simpa [hk_eq] using hL_diag
  L_upper_zero_done := by
    intro i j hj hij
    have hle : j.val ≤ t := Nat.lt_succ_iff.mp hj
    by_cases hjt : j.val < t
    · exact hprev.L_upper_zero_done i j hjt hij
    · have hjval : j.val = t := le_antisymm hle (Nat.le_of_not_gt hjt)
      have hj_eq : j = (⟨t, ht⟩ : Fin n) := Fin.ext hjval
      simpa [hj_eq] using hL_upper_zero_stage i (by simpa [hj_eq] using hij)
  U_lower_zero_done := by
    intro i j hi hji
    have hle : i.val ≤ t := Nat.lt_succ_iff.mp hi
    by_cases hit : i.val < t
    · exact hprev.U_lower_zero_done i j hit hji
    · have hival : i.val = t := le_antisymm hle (Nat.le_of_not_gt hit)
      have hi_eq : i = (⟨t, ht⟩ : Fin n) := Fin.ext hival
      simpa [hi_eq] using hU_lower_zero_stage j (by simpa [hi_eq] using hji)
  U_stage_eq_done := by
    intro k j hk hkj
    have hle : k.val ≤ t := Nat.lt_succ_iff.mp hk
    by_cases hkt : k.val < t
    · exact hprev.U_stage_eq_done k j hkt hkj
    · have hkval : k.val = t := le_antisymm hle (Nat.le_of_not_gt hkt)
      have hk_eq : k = (⟨t, ht⟩ : Fin n) := Fin.ext hkval
      simpa [hk_eq] using hU_stage_eq j (by simpa [hk_eq] using hkj)
  L_stage_eq_done := by
    intro i k hk hki
    have hle : k.val ≤ t := Nat.lt_succ_iff.mp hk
    by_cases hkt : k.val < t
    · exact hprev.L_stage_eq_done i k hkt hki
    · have hkval : k.val = t := le_antisymm hle (Nat.le_of_not_gt hkt)
      have hk_eq : k = (⟨t, ht⟩ : Fin n) := Fin.ext hkval
      simpa [hk_eq] using hL_stage_eq i (by simpa [hk_eq] using hki)

/-- **Algorithm 9.2**, rectangular rounded prefix trace from natural-number
stage obligations.  If every stage `t < n` supplies the diagonal, triangular
shape, upper-row fold, and lower-column fold obligations for that stage, then
the prefix trace can be assembled for any horizon `T <= n`. -/
theorem higham9_2_rectRoundedPrefixTrace_of_stage_obligations
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ (t : ℕ) (ht : t < n),
      L (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, i.val < t → L i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, j.val < t → U ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, t ≤ j.val →
        U ⟨t, ht⟩ j =
          higham9_2_rectFlDoolittleUEntry fp hmn A L U ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, t < i.val →
        L i ⟨t, ht⟩ =
          higham9_2_rectFlDoolittleLEntry fp A L U i ⟨t, ht⟩) :
    ∀ T : ℕ, T ≤ n →
      higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp T := by
  intro T
  induction T with
  | zero =>
      intro _hT
      exact higham9_2_rectRoundedPrefixTrace_zero
  | succ t ih =>
      intro hT
      have ht : t < n := Nat.lt_of_succ_le hT
      exact
        higham9_2_rectRoundedPrefixTrace_succ ht
          (ih (Nat.le_of_lt ht))
          (hL_diag t ht)
          (hL_upper_zero_stage t ht)
          (hU_lower_zero_stage t ht)
          (hU_stage_eq t ht)
          (hL_stage_eq t ht)

/-- **Algorithm 9.2**, complete rectangular rounded prefix trace from
natural-number stage obligations. -/
theorem higham9_2_rectRoundedPrefixTrace_complete_of_stage_obligations
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ (t : ℕ) (ht : t < n),
      L (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, i.val < t → L i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, j.val < t → U ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, t ≤ j.val →
        U ⟨t, ht⟩ j =
          higham9_2_rectFlDoolittleUEntry fp hmn A L U ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, t < i.val →
        L i ⟨t, ht⟩ =
          higham9_2_rectFlDoolittleLEntry fp A L U i ⟨t, ht⟩) :
    higham9_2_RectDoolittleRoundedPrefixTrace hmn A L U fp n :=
  higham9_2_rectRoundedPrefixTrace_of_stage_obligations
    hL_diag hL_upper_zero_stage hU_lower_zero_stage hU_stage_eq hL_stage_eq
    n (Nat.le_refl n)

/-- **Algorithm 9.2**, full rectangular rounded-stage trace from natural-number
stage obligations. -/
theorem higham9_2_rectRoundedStageTrace_of_stage_obligations
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ (t : ℕ) (ht : t < n),
      L (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, i.val < t → L i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, j.val < t → U ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, t ≤ j.val →
        U ⟨t, ht⟩ j =
          higham9_2_rectFlDoolittleUEntry fp hmn A L U ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, t < i.val →
        L i ⟨t, ht⟩ =
          higham9_2_rectFlDoolittleLEntry fp A L U i ⟨t, ht⟩) :
    higham9_2_RectDoolittleRoundedStageTrace hmn A L U fp :=
  higham9_2_rectRoundedPrefixTrace_complete_to_stageTrace
    (higham9_2_rectRoundedPrefixTrace_complete_of_stage_obligations
      hL_diag hL_upper_zero_stage hU_lower_zero_stage hU_stage_eq hL_stage_eq)

/-- **Algorithm 9.2**, rectangular dense-loop certificate from natural-number
stage obligations, nonbreakdown, and visible budget dominance. -/
theorem higham9_2_rectStageObligations_to_rectDenseLoopCertificate
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ (t : ℕ) (ht : t < n),
      L (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, i.val < t → L i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, j.val < t → U ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, t ≤ j.val →
        U ⟨t, ht⟩ j =
          higham9_2_rectFlDoolittleUEntry fp hmn A L U ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, t < i.val →
        L i ⟨t, ht⟩ =
          higham9_2_rectFlDoolittleLEntry fp A L U i ⟨t, ht⟩)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L U k j ≤
        gamma fp n * |U k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopCertificate hmn A L U fp :=
  higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
    (higham9_2_rectRoundedStageTrace_of_stage_obligations
      hL_diag hL_upper_zero_stage hU_lower_zero_stage hU_stage_eq hL_stage_eq)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, rectangular componentwise dominance handoff.  Visible
upper work/product dominance, lower work/product/numerator dominance, and the
explicit lower coefficient compression condition imply the rectangular
literal absolute-budget certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUWorkAbs fp hmn A L U k j ≤ |U k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|)
    (hL_work_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLWorkAbs fp A L U i k ≤
        |L i k * U k k|)
    (hL_prod_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|)
    (hL_num_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L U i k ≤
        |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) := by
  exact
    higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn
      (by
        intro k j hkj
        exact
          higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance
            (hmn := hmn) (A := A) (L := L) (U := U)
            hn hkj (hU_work_le k j hkj) (hU_prod_le k j hkj))
      (by
        intro i k hki
        have hk : gammaValid fp k.val :=
          gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
        exact
          higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance
            (A := A) (L := L) (U := U) hki (hL_coeff i k hki)
            (hL_work_le i k hki) (hL_prod_le i k hki)
            (hL_num_le i k hki) hk)

/-- **Algorithm 9.2**, rectangular exact-product no-cancellation handoff.
Exact-product upper/lower margins, an explicit lower rounded-numerator
dominance condition, and the rectangular lower coefficient compression
condition produce the rectangular literal absolute-budget certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|)
    (hL_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|)
    (hL_num_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L U i k ≤
        |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) := by
  exact
    higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff
      (by
        intro k j hkj
        exact
          higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin
            (hmn := hmn) (A := A) (L := L) (U := U)
            (hU_margin k j hkj))
      (by
        intro k j hkj
        exact
          higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin
            (hmn := hmn) (A := A) (L := L) (U := U)
            (hU_margin k j hkj))
      (by
        intro i k hki
        exact
          higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin
            (A := A) (L := L) (U := U) (hL_margin i k hki))
      (by
        intro i k hki
        exact
          higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin
            (A := A) (L := L) (U := U) (hL_margin i k hki))
      hL_num_le

/-- **Algorithm 9.2**, rectangular exact-product numerator-margin handoff.
Exact-product upper/lower margins plus an explicit lower numerator margin
produce the rectangular literal absolute-budget certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j ≤ |U k j|)
    (hL_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k ≤
        |L i k * U k k|)
    (hL_num_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      (|A i k| + higham9_2_rectDoolittleLProductAbs fp A L U i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              higham9_2_rectDoolittleLProductAbs fp A L U i k) +
          fp.u * higham9_2_rectDoolittleLProductAbs fp A L U i k) ≤
        |L i k * U k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) := by
  refine
    higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_margin hL_margin ?_
  intro i k hki
  have hk : gammaValid fp k.val :=
    gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
  exact
    higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin
      (A := A) (L := L) (U := U) hk (hL_num_margin i k hki)

/-- **Algorithm 9.2**, rectangular exact-target gap handoff.  Source-visible
gaps for the rectangular literal rounded Doolittle upper and lower targets,
together with the rectangular lower coefficient compression condition, produce
the rectangular literal absolute-budget certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectFlDoolittleUEntry fp hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectFlDoolittleLEntry fp A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L U k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp hmn A L U k j ≤
        |higham9_2_rectDoolittleUExactTarget hmn A L U k j|)
    (hL_gap : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L U i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp A L U i k ≤
        |higham9_2_rectDoolittleLExactTarget A L U i k|)
    (hL_num_gap : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L U i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L U i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L U i k ≤
        |higham9_2_rectDoolittleLExactTarget A L U i k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate hmn A L U fp
      (higham9_2_rectDoolittleUAbsBudget fp hmn A L U)
      (higham9_2_rectDoolittleLAbsBudget fp A L U) := by
  refine
    higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff ?_ ?_ ?_
  · intro k j hkj
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    exact
      higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap
        (hmn := hmn) (A := A) (L := L) (U := U)
        hk (hU_entry_eq k j hkj) (hU_gap k j hkj)
  · intro i k hki
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    exact
      higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap
        (A := A) (L := L) (U := U)
        hk (hU_diag k) (hL_entry_eq i k hki) (hL_gap i k hki)
  · intro i k hki
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    simpa [higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget] using
      higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap
        (A := A) (L := L) (U := U)
        hk (hU_diag k) (hL_entry_eq i k hki) (hL_num_gap i k hki)

/-- **Algorithm 9.2**, square specialization of the rectangular dense-loop
certificate.  At `m = n`, the source-shaped rectangular certificate is exactly
the existing square dense-loop certificate used by Theorem 9.3. -/
theorem higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L U fp) :
    DoolittleDenseLoopCertificate n A L U fp where
  L_diag := by
    intro i
    simpa [higham9_2_rectRow] using hC.L_diag i
  L_upper_zero := hC.L_upper_zero
  U_lower_zero := hC.U_lower_zero
  U_entry_eq := by
    intro k j hkj
    simpa [higham9_2_rectFlDoolittleUEntry, higham9_2_rectRow] using
      hC.U_entry_eq k j hkj
  L_entry_eq := by
    intro i k hki
    simpa [higham9_2_rectFlDoolittleLEntry,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLEntry,
      flDoolittleLNumerator] using hC.L_entry_eq i k hki
  U_residual_compression := by
    intro k j hkj
    simpa [higham9_2_rectPrefixDot, higham9_2_rectRow] using
      hC.U_residual_compression k j hkj
  L_residual_compression := by
    intro i k hki
    simpa [higham9_2_rectPrefixDot] using
      hC.L_residual_compression i k hki

/-- **Algorithm 9.2**, square specialization of the rectangular absolute-budget
certificate.  A rectangular certificate at `m = n` feeds the existing square
`DoolittleDenseLoopAbsBudgetCertificate` API, so rectangular loop work can reuse
the established Theorem 9.3 dense-Doolittle handoff in the square case. -/
theorem higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {BU BL : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L U fp BU BL) :
    DoolittleDenseLoopAbsBudgetCertificate n A L U fp BU BL where
  L_diag := by
    intro i
    simpa [higham9_2_rectRow] using hC.L_diag i
  L_upper_zero := hC.L_upper_zero
  U_lower_zero := hC.U_lower_zero
  U_entry_eq := by
    intro k j hkj
    simpa [higham9_2_rectFlDoolittleUEntry, higham9_2_rectRow] using
      hC.U_entry_eq k j hkj
  L_entry_eq := by
    intro i k hki
    simpa [higham9_2_rectFlDoolittleLEntry,
      higham9_2_rectFlDoolittleLNumerator, flDoolittleLEntry,
      flDoolittleLNumerator] using hC.L_entry_eq i k hki
  U_abs_residual := by
    intro k j hkj
    simpa [higham9_2_rectPrefixDot, higham9_2_rectRow] using
      hC.U_abs_residual k j hkj
  U_budget_le_compression := hC.U_budget_le_compression
  L_abs_residual := by
    intro i k hki
    simpa [higham9_2_rectPrefixDot] using hC.L_abs_residual i k hki
  L_budget_le_compression := hC.L_budget_le_compression

/-- **Algorithm 9.2**, square-specialized rectangular dense-loop certificate
as the compact `DoolittleLU` recurrence certificate. -/
theorem higham9_2_rectDenseLoopCertificate_square_to_DoolittleLU
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L U fp)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L U fp :=
  higham9_2_denseLoopCertificate_to_DoolittleLU
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC) hn

/-- **Algorithm 9.2**, square-specialized rectangular absolute-budget
certificate as the compact `DoolittleLU` recurrence certificate. -/
theorem higham9_2_rectAbsBudgetCertificate_square_to_DoolittleLU
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ} {BU BL : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L U fp BU BL)
    (hn : gammaValid fp n) :
    higham9_2_DoolittleLU n A L U fp :=
  higham9_2_absBudgetCertificate_to_DoolittleLU
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC) hn

/-- **Algorithm 9.2**, square-specialized rectangular rounded-stage trace as
the compact `DoolittleLU` recurrence certificate. -/
theorem higham9_2_rectRoundedStageTrace_square_to_DoolittleLU
    {n : ℕ} {fp : FPModel}
    {A L U : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) A L U fp)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L U k j ≤
        gamma fp n * |U k j|)
    (hL_budget_le : ∀ i : Fin n, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k|) :
    higham9_2_DoolittleLU n A L U fp :=
  higham9_2_rectAbsBudgetCertificate_square_to_DoolittleLU
    (higham9_2_rectRoundedStageTrace_to_rectAbsBudgetCertificate
      hT hU_diag hn hU_budget_le hL_budget_le) hn

/-- **Algorithm 9.2**, square-specialized executable rectangular rounded loop as
the compact `DoolittleLU` recurrence certificate. -/
theorem higham9_2_rectRoundedLoop_square_to_DoolittleLU {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i : Fin n, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    higham9_2_DoolittleLU n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) fp :=
  higham9_2_rectRoundedStageTrace_square_to_DoolittleLU
    (higham9_2_rectRoundedLoopStageTrace fp (Nat.le_refl n) A)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2 / Theorem 9.3**, row-pivoted rectangular dense-loop
handoff.

This is the certificate-level bridge from a square-specialized rectangular
Doolittle certificate for `PA` to Higham's row-pivoted backward-error surface. -/
theorem higham9_2_permutedRectDenseLoopCertificate_to_PermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp) :
    higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) :=
  higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError
    hsigma hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)

/-- **Algorithm 9.2 / Theorem 9.3**, row-pivoted rectangular absolute-budget
handoff.

The rectangular absolute-budget certificate at `m = n` reuses the established
square absolute-budget compression before entering the pivoted certificate API. -/
theorem higham9_2_permutedRectAbsBudgetCertificate_to_PermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp BU BL) :
    higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) :=
  higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError
    hsigma hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)

/-- **Algorithm 9.2 / Theorem 9.3**, row-pivoted rectangular rounded-stage
trace handoff.

A rectangular rounded trace for the already row-permuted matrix `PA`, together
with the visible absolute-budget dominance hypotheses, supplies the standard
pivoted backward-error certificate. -/
theorem higham9_2_permutedRectRoundedStageTrace_to_PermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) :=
  higham9_2_permutedRectDenseLoopCertificate_to_PermutedLUBackwardError
    hsigma hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Algorithm 9.2 / Theorem 9.3**, executable row-pivoted rectangular
rounded-loop trace production.

The concrete rectangular Doolittle loop run on the row-permuted matrix `PA`
produces the same rounded-stage trace object consumed by the pivoted
backward-error wrappers. -/
theorem higham9_2_permutedRectRoundedLoopStageTrace {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n) :
    higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)) fp :=
  higham9_2_rectRoundedLoopStageTrace fp (Nat.le_refl n)
    (higham9_2_rowPermutedMatrix A sigma)

/-- **Algorithm 9.2 / Theorem 9.3**, executable row-pivoted rectangular
rounded-loop absolute-budget certificate production.

The concrete rectangular Doolittle loop run on the row-permuted matrix `PA`
also supplies the absolute-budget certificate used by downstream compressed
and dense-loop backward-error wrappers. -/
theorem higham9_2_permutedRectRoundedLoop_to_rectAbsBudgetCertificate
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)) fp
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma))
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)))
      (higham9_2_rectDoolittleLAbsBudget fp
        (higham9_2_rowPermutedMatrix A sigma)
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma))
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma))) :=
  higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate
    fp (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2 / Theorem 9.3**, executable row-pivoted rectangular
rounded-loop dense-certificate production.

This is the named dense-loop certificate produced by running the executable
rectangular Doolittle loop on `PA`, under the usual nonzero-pivot and visible
absolute-budget dominance hypotheses. -/
theorem higham9_2_permutedRectRoundedLoop_to_rectDenseLoopCertificate
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)) fp :=
  higham9_2_rectRoundedLoop_to_rectDenseLoopCertificate
    fp (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, executable row-pivoted rectangular loop as a compact
`DoolittleLU` recurrence certificate for the row-permuted matrix `PA`. -/
theorem higham9_2_permutedRectRoundedLoop_square_to_DoolittleLU {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    higham9_2_DoolittleLU n (higham9_2_rowPermutedMatrix A sigma)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)) fp :=
  higham9_2_rectRoundedLoop_square_to_DoolittleLU
    fp (higham9_2_rowPermutedMatrix A sigma)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2 / Theorem 9.3**, executable row-pivoted rectangular loop
handoff.

Running the concrete rectangular rounded Doolittle loop on `PA` gives a
row-pivoted backward-error certificate once the usual nonzero-pivot and
visible budget-dominance hypotheses are supplied. -/
theorem higham9_2_permutedRectRoundedLoop_to_PermutedLUBackwardError
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (hsigma : IsPermutation n sigma)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    higham9_2_PermutedLUBackwardError n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma))
      sigma (gamma fp n) :=
  higham9_2_permutedRectDenseLoopCertificate_to_PermutedLUBackwardError
    (A := A) (sigma := sigma) hsigma hn
    (higham9_2_permutedRectRoundedLoop_to_rectDenseLoopCertificate
      fp A sigma hU_diag hn hU_budget_le hL_budget_le)

/-- **Algorithm 9.2 / Theorem 9.3**, complete-pivoted rectangular dense-loop
handoff.

This packages a square-specialized rectangular Doolittle certificate for
`PAQ` as Higham's complete-pivoted backward-error certificate. -/
theorem
    higham9_2_completePermutedRectDenseLoopCertificate_to_CompletePermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp) :
    higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n) :=
  higham9_2_completePermutedDenseLoopCertificate_to_CompletePermutedLUBackwardError
    hsigma htau hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)

/-- **Algorithm 9.2 / Theorem 9.3**, complete-pivoted rectangular
absolute-budget handoff. -/
theorem
    higham9_2_completePermutedRectAbsBudgetCertificate_to_CompletePermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp BU BL) :
    higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n) :=
  higham9_2_completePermutedAbsBudgetCertificate_to_CompletePermutedLUBackwardError
    hsigma htau hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)

/-- **Algorithm 9.2 / Theorem 9.3**, complete-pivoted rectangular
rounded-stage trace handoff. -/
theorem
    higham9_2_completePermutedRectRoundedStageTrace_to_CompletePermutedLUBackwardError
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n) :=
  higham9_2_completePermutedRectDenseLoopCertificate_to_CompletePermutedLUBackwardError
    hsigma htau hn
    (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Algorithm 9.2 / Theorem 9.3**, executable complete-pivoted rectangular
rounded-loop trace production.

The concrete rectangular Doolittle loop run on `PAQ` produces the
rounded-stage trace object consumed by the complete-pivoted backward-error
wrappers. -/
theorem higham9_2_completePermutedRectRoundedLoopStageTrace {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (sigma tau : Fin n → Fin n) :
    higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau)) fp :=
  higham9_2_rectRoundedLoopStageTrace fp (Nat.le_refl n)
    (higham9_2_rowColPermutedMatrix A sigma tau)

/-- **Algorithm 9.2 / Theorem 9.3**, executable complete-pivoted rectangular
rounded-loop absolute-budget certificate production.

The concrete rectangular Doolittle loop run on `PAQ` supplies the absolute-
budget certificate consumed before the complete-pivoted dense-loop
backward-error surface. -/
theorem higham9_2_completePermutedRectRoundedLoop_to_rectAbsBudgetCertificate
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau)) fp
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau)
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau))
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)))
      (higham9_2_rectDoolittleLAbsBudget fp
        (higham9_2_rowColPermutedMatrix A sigma tau)
        (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau))
        (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau))) :=
  higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate
    fp (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2 / Theorem 9.3**, executable complete-pivoted rectangular
rounded-loop dense-certificate production.

This is the named dense-loop certificate produced by running the executable
rectangular Doolittle loop on `PAQ`, under the usual nonzero-pivot and visible
absolute-budget dominance hypotheses. -/
theorem higham9_2_completePermutedRectRoundedLoop_to_rectDenseLoopCertificate
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau)) fp :=
  higham9_2_rectRoundedLoop_to_rectDenseLoopCertificate
    fp (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2**, executable complete-pivoted rectangular loop as a
compact `DoolittleLU` recurrence certificate for the row/column-permuted matrix
`PAQ`. -/
theorem higham9_2_completePermutedRectRoundedLoop_square_to_DoolittleLU
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    higham9_2_DoolittleLU n (higham9_2_rowColPermutedMatrix A sigma tau)
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau)) fp :=
  higham9_2_rectRoundedLoop_square_to_DoolittleLU
    fp (higham9_2_rowColPermutedMatrix A sigma tau)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Algorithm 9.2 / Theorem 9.3**, executable complete-pivoted rectangular
loop handoff.

The concrete rectangular rounded Doolittle loop on `PAQ` feeds the
complete-pivoted backward-error certificate under the same local pivot and
budget-dominance side conditions as the unpivoted rectangular loop. -/
theorem
    higham9_2_completePermutedRectRoundedLoop_to_CompletePermutedLUBackwardError
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    higham9_2_CompletePermutedLUBackwardError n A
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowColPermutedMatrix A sigma tau))
      sigma tau (gamma fp n) :=
  higham9_2_completePermutedRectDenseLoopCertificate_to_CompletePermutedLUBackwardError
    (A := A) (sigma := sigma) (tau := tau) hsigma htau hn
    (higham9_2_completePermutedRectRoundedLoop_to_rectDenseLoopCertificate
      fp A sigma tau hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, row-pivoted rectangular dense-loop perturbation form.

This exposes the `PA + ΔPA` theorem directly from a square-specialized
rectangular dense-loop certificate for `PA`. -/
theorem higham9_3_permuted_rectDenseLoopCertificate_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  higham9_3_permuted_lu_backward_error_gamma hn
    (higham9_2_permutedRectDenseLoopCertificate_to_PermutedLUBackwardError
      hsigma hn hC)

/-- **Theorem 9.3**, row-pivoted rectangular absolute-budget perturbation
form. -/
theorem higham9_3_permuted_rectAbsBudgetCertificate_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp BU BL) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  higham9_3_permuted_lu_backward_error_gamma hn
    (higham9_2_permutedRectAbsBudgetCertificate_to_PermutedLUBackwardError
      hsigma hn hC)

/-- **Theorem 9.3**, row-pivoted rectangular rounded-stage perturbation form. -/
theorem higham9_3_permuted_rectRoundedStageTrace_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma)
      L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  higham9_3_permuted_lu_backward_error_gamma hn
    (higham9_2_permutedRectRoundedStageTrace_to_PermutedLUBackwardError
      hsigma hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, executable row-pivoted rectangular rounded-loop
perturbation form. -/
theorem higham9_3_permuted_rectRoundedLoop_backward_error
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (hsigma : IsPermutation n sigma)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    ∃ ΔPA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPA i j| ≤
          gamma fp n * ∑ k : Fin n,
            |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k j|) ∧
      (∀ i j,
        ∑ k : Fin n,
            higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k j =
          higham9_2_rowPermutedMatrix A sigma i j + ΔPA i j) :=
  higham9_3_permuted_lu_backward_error_gamma hn
    (higham9_2_permutedRectRoundedLoop_to_PermutedLUBackwardError
      fp A sigma hsigma hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, complete-pivoted rectangular dense-loop perturbation
form. -/
theorem higham9_3_complete_permuted_rectDenseLoopCertificate_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  higham9_3_complete_permuted_lu_backward_error_gamma hn
    (higham9_2_completePermutedRectDenseLoopCertificate_to_CompletePermutedLUBackwardError
      hsigma htau hn hC)

/-- **Theorem 9.3**, complete-pivoted rectangular absolute-budget
perturbation form. -/
theorem higham9_3_complete_permuted_rectAbsBudgetCertificate_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    {BU BL : Fin n → Fin n → ℝ}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp BU BL) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  higham9_3_complete_permuted_lu_backward_error_gamma hn
    (higham9_2_completePermutedRectAbsBudgetCertificate_to_CompletePermutedLUBackwardError
      hsigma htau hn hC)

/-- **Theorem 9.3**, complete-pivoted rectangular rounded-stage perturbation
form. -/
theorem higham9_3_complete_permuted_rectRoundedStageTrace_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowColPermutedMatrix A sigma tau)
      L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j,
        ∑ k : Fin n, L_hat i k * U_hat k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  higham9_3_complete_permuted_lu_backward_error_gamma hn
    (higham9_2_completePermutedRectRoundedStageTrace_to_CompletePermutedLUBackwardError
      hsigma htau hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, executable complete-pivoted rectangular rounded-loop
perturbation form. -/
theorem higham9_3_complete_permuted_rectRoundedLoop_backward_error
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    ∃ ΔPAQ : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔPAQ i j| ≤
          gamma fp n * ∑ k : Fin n,
            |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k j|) ∧
      (∀ i j,
        ∑ k : Fin n,
            higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k j =
          higham9_2_rowColPermutedMatrix A sigma tau i j + ΔPAQ i j) :=
  higham9_3_complete_permuted_lu_backward_error_gamma hn
    (higham9_2_completePermutedRectRoundedLoop_to_CompletePermutedLUBackwardError
      fp A sigma tau hsigma htau hU_diag hn hU_budget_le hL_budget_le)

/-- **Algorithm 9.2**, rectangular product split for an upper entry:
triangular support reduces the stored product to the prefix dot plus the
computed upper entry. -/
theorem higham9_2_rectMatMul_eq_prefix_add_upper {m n : ℕ} {hmn : n ≤ m}
    {L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (k j : Fin n) (_hkj : k.val ≤ j.val) :
    rectMatMul L U (higham9_2_rectRow hmn k) j =
      higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k + U k j := by
  unfold rectMatMul higham9_2_rectPrefixDot
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : Fin n => s.val < k.val)
    (fun s : Fin n => L (higham9_2_rectRow hmn k) s * U s j)]
  congr 1
  · simp [Finset.sum_filter]
  · rw [Finset.sum_eq_single k]
    · simp [hL_diag k]
    · intro s hs hsk
      have hnotlt : ¬ s.val < k.val := (Finset.mem_filter.mp hs).2
      have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
      have hne_val : k.val ≠ s.val := by
        intro hval
        exact hsk (Fin.ext hval.symm)
      have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
      have hrow_lt : (higham9_2_rectRow hmn k).val < s.val := by
        simpa [higham9_2_rectRow] using hk_lt_s
      rw [hL_upper_zero (higham9_2_rectRow hmn k) s hrow_lt, zero_mul]
    · intro hk_not_mem
      exact (hk_not_mem (by simp)).elim

/-- **Algorithm 9.2**, rectangular product split for a lower entry:
upper-triangular support of `U` reduces the stored product to the prefix dot
plus the lower multiplier times the pivot. -/
theorem higham9_2_rectMatMul_eq_prefix_add_lower {m n : ℕ}
    {L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin m) (k : Fin n) :
    rectMatMul L U i k =
      higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  unfold rectMatMul higham9_2_rectPrefixDot
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : Fin n => s.val < k.val)
    (fun s : Fin n => L i s * U s k)]
  congr 1
  · simp [Finset.sum_filter]
  · rw [Finset.sum_eq_single k]
    · intro s hs hsk
      have hnotlt : ¬ s.val < k.val := (Finset.mem_filter.mp hs).2
      have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
      have hne_val : k.val ≠ s.val := by
        intro hval
        exact hsk (Fin.ext hval.symm)
      have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
      rw [hU_lower_zero s k hk_lt_s, mul_zero]
    · intro hk_not_mem
      exact (hk_not_mem (by simp)).elim

/-- **Algorithm 9.2**, the upper stored entry is one term in the absolute
rectangular product sum. -/
theorem higham9_2_abs_upper_entry_le_rectMatMul_abs_sum {m n : ℕ}
    {hmn : n ≤ m} {L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (k j : Fin n) :
    |U k j| ≤
      ∑ s : Fin n, |L (higham9_2_rectRow hmn k) s| * |U s j| := by
  have hterm :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun s : Fin n =>
        |L (higham9_2_rectRow hmn k) s| * |U s j|)
      (fun s _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ k :
        k ∈ (Finset.univ : Finset (Fin n)))
  simpa [hL_diag k] using hterm

/-- **Algorithm 9.2**, the lower stored product is one term in the absolute
rectangular product sum. -/
theorem higham9_2_abs_lower_entry_mul_pivot_le_rectMatMul_abs_sum {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) :
    |L i k * U k k| ≤
      ∑ s : Fin n, |L i s| * |U s k| := by
  have hterm :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun s : Fin n => |L i s| * |U s k|)
      (fun s _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ k :
        k ∈ (Finset.univ : Finset (Fin n)))
  simpa [abs_mul] using hterm

/-- **Equation (9.3)** source identity for the rectangular Doolittle upper
update: the exact assignment restores the displayed prefix-sum equation. -/
theorem higham9_2_rectDoolittleUUpdate_source_identity {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k +
      higham9_2_rectDoolittleUUpdate hmn A L U k j =
        A (higham9_2_rectRow hmn k) j := by
  unfold higham9_2_rectDoolittleUUpdate
  ring

/-- **Equation (9.3)** in source orientation: if the stored upper entry is the
rectangular Doolittle update, then `a_kj` is the prefix dot product plus
`u_kj`. -/
theorem higham9_2_rectDoolittleU_source_identity {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n)
    (hU :
      U k j = higham9_2_rectDoolittleUUpdate hmn A L U k j) :
    A (higham9_2_rectRow hmn k) j =
      higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k +
        U k j := by
  rw [hU]
  symm
  exact higham9_2_rectDoolittleUUpdate_source_identity hmn A L U k j

/-- **Equation (9.4)** source identity for the rectangular Doolittle lower
update: after division by a nonzero pivot and multiplication back by the same
pivot, the exact assignment restores the displayed prefix-sum equation. -/
theorem higham9_2_rectDoolittleLUpdate_source_identity {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0) :
    higham9_2_rectPrefixDot L U i k k +
      higham9_2_rectDoolittleLUpdate A L U i k * U k k =
        A i k := by
  unfold higham9_2_rectDoolittleLUpdate
  rw [div_mul_cancel₀ _ hUkk]
  ring

/-- **Equation (9.4)** in source orientation: if the stored lower entry is the
rectangular Doolittle update and the pivot is nonzero, then `a_ik` is the prefix
dot product plus `l_ik u_kk`. -/
theorem higham9_2_rectDoolittleL_source_identity {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0)
    (hL : L i k = higham9_2_rectDoolittleLUpdate A L U i k) :
    A i k =
      higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  rw [hL]
  symm
  exact higham9_2_rectDoolittleLUpdate_source_identity A L U i k hUkk

/-- **Algorithm 9.2**, exact rectangular recurrence product bridge.  If the
stored rectangular factors satisfy the exact upper and lower Doolittle update
equations, with unit rectangular pivot rows and nonzero pivots, then their
rectangular product is the source matrix.  This closes the exact
recurrence-to-product handoff used by the rectangular equation (9.5) layer;
the rounded executable schedule remains a separate certificate-production
problem. -/
theorem higham9_2_rectDoolittle_exact_recurrences_rectMatMul_eq {m n : ℕ}
    {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    ∀ i j, rectMatMul L U i j = A i j := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · let k : Fin n := ⟨i.val, lt_of_le_of_lt hij j.isLt⟩
    have hi_row : higham9_2_rectRow hmn k = i := by
      ext
      rfl
    have hkj : k.val ≤ j.val := by
      simpa [k] using hij
    have hprod :=
      higham9_2_rectMatMul_eq_prefix_add_upper
        (hmn := hmn) (L := L) (U := U)
        hL_diag hL_upper_zero k j hkj
    have hsource :=
      higham9_2_rectDoolittleU_source_identity
        hmn A L U k j (hU_entry_eq k j hkj)
    calc
      rectMatMul L U i j =
          rectMatMul L U (higham9_2_rectRow hmn k) j := by
            rw [hi_row]
      _ = higham9_2_rectPrefixDot L U (higham9_2_rectRow hmn k) j k +
            U k j := hprod
      _ = A (higham9_2_rectRow hmn k) j := by
            rw [← hsource]
      _ = A i j := by
            rw [hi_row]
  · have hji : j.val < i.val := lt_of_not_ge hij
    have hprod :=
      higham9_2_rectMatMul_eq_prefix_add_lower
        (L := L) (U := U) hU_lower_zero i j
    have hsource :=
      higham9_2_rectDoolittleL_source_identity
        A L U i j (hU_diag j) (hL_entry_eq i j hji)
    calc
      rectMatMul L U i j =
          higham9_2_rectPrefixDot L U i j j + L i j * U j j := hprod
      _ = A i j := by
            rw [← hsource]

/-- **Algorithm 9.2**, exact square Doolittle recurrences as an exact
`LUFactSpec`.  This is the source-facing square specialization of the
rectangular recurrence product bridge: exact upper and lower Doolittle updates
plus triangular shape, unit lower diagonal, and nonzero pivots give an ordinary
exact LU certificate.  It still does not construct the rounded executable loop
that would prove these recurrence hypotheses for computed factors. -/
theorem higham9_2_exactDoolittle_recurrences_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    LUFactSpec n A L U where
  L_diag := hL_diag
  L_upper_zero := hL_upper_zero
  U_lower_zero := hU_lower_zero
  product_eq := by
    intro i j
    have hprod :=
      higham9_2_rectDoolittle_exact_recurrences_rectMatMul_eq
        (hmn := Nat.le_refl n) (A := A) (L := L) (U := U)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag i j
    simpa [rectMatMul] using hprod

/-- **Algorithm 9.2 / Theorem 9.1 support**, exact-LU upper recurrence.
Every exact unit-lower/upper `LUFactSpec` satisfies the Doolittle upper-entry
formula used in equation (9.3).  This is the converse direction of the source
identity above, restricted to the square exact-LU certificate surface. -/
theorem higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (k j : Fin n) :
    U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j := by
  classical
  have hprod := hLU.product_eq k j
  have hsum :
      (∑ s : Fin n, L k s * U s j) =
        higham9_2_rectPrefixDot L U k j k + U k j := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s : Fin n => s.val < k.val)
      (fun s : Fin n => L k s * U s j)]
    congr 1
    · simp [higham9_2_rectPrefixDot, Finset.sum_filter]
    · rw [Finset.sum_eq_single k]
      · simp [hLU.L_diag k]
      · intro s hs hsk
        have hnotlt : ¬ s.val < k.val := by
          exact (Finset.mem_filter.mp hs).2
        have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
        have hne_val : k.val ≠ s.val := by
          intro hval
          exact hsk (Fin.ext hval.symm)
        have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
        rw [hLU.L_upper_zero k s hk_lt_s, zero_mul]
      · intro hk_not_mem
        exact (hk_not_mem (by simp)).elim
  have hA :
      A k j = higham9_2_rectPrefixDot L U k j k + U k j := by
    rw [← hprod, hsum]
  unfold higham9_2_rectDoolittleUUpdate
  simp [higham9_2_rectRow, hA]

/-- **Algorithm 9.2 / Theorem 9.1 support**, exact-LU lower recurrence.
Every exact unit-lower/upper `LUFactSpec` with a nonzero pivot satisfies the
Doolittle lower-entry formula used in equation (9.4).  This is a local
dependency for uniqueness/existence work; it does not construct the factorization. -/
theorem higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (i k : Fin n)
    (hUkk : U k k ≠ 0) :
    L i k = higham9_2_rectDoolittleLUpdate A L U i k := by
  classical
  have hprod := hLU.product_eq i k
  have hsum :
      (∑ s : Fin n, L i s * U s k) =
        higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s : Fin n => s.val < k.val)
      (fun s : Fin n => L i s * U s k)]
    congr 1
    · simp [higham9_2_rectPrefixDot, Finset.sum_filter]
    · rw [Finset.sum_eq_single k]
      · intro s hs hsk
        have hnotlt : ¬ s.val < k.val := by
          exact (Finset.mem_filter.mp hs).2
        have hle : k.val ≤ s.val := Nat.le_of_not_gt hnotlt
        have hne_val : k.val ≠ s.val := by
          intro hval
          exact hsk (Fin.ext hval.symm)
        have hk_lt_s : k.val < s.val := lt_of_le_of_ne hle hne_val
        rw [hLU.U_lower_zero s k hk_lt_s, mul_zero]
      · intro hk_not_mem
        exact (hk_not_mem (by simp)).elim
  have hA :
      A i k = higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
    rw [← hprod, hsum]
  unfold higham9_2_rectDoolittleLUpdate
  rw [hA]
  field_simp [hUkk]
  ring

/-- **Theorem 9.1 support**, uniqueness of an exact LU certificate once the
pivots are nonzero.  The proof follows the Doolittle recurrences column by
column: previous columns of `L` and rows of `U` determine the next row of `U`,
then the nonzero pivot determines the next column of `L`.  This is still only
the uniqueness half of Theorem 9.1; it does not construct factors from leading
principal minors. -/
theorem higham9_1_lu_unique_of_pivots_ne_zero {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂)
    (hU₁diag : ∀ k : Fin n, U₁ k k ≠ 0) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  classical
  have hstage :
      ∀ t : ℕ, t ≤ n →
        ∀ k : Fin n, k.val < t →
          (∀ j : Fin n, U₁ k j = U₂ k j) ∧
            (∀ i : Fin n, L₁ i k = L₂ i k) := by
    intro t
    induction t with
    | zero =>
        intro _ k hk
        exact (Nat.not_lt_zero _ hk).elim
    | succ t ih =>
        intro ht k hk
        have ht_le : t ≤ n := Nat.le_trans (Nat.le_succ t) ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact ih ht_le k hk_lt
        · have ht_lt_n : t < n := Nat.lt_of_succ_le ht
          let kk : Fin n := ⟨t, ht_lt_n⟩
          have hk_eq_fin : k = kk := Fin.ext hk_eq
          subst k
          have hprev :
              ∀ s : Fin n, s.val < kk.val →
                (∀ j : Fin n, U₁ s j = U₂ s j) ∧
                  (∀ i : Fin n, L₁ i s = L₂ i s) := by
            intro s hs
            exact ih ht_le s hs
          have hUeq : ∀ j : Fin n, U₁ kk j = U₂ kk j := by
            intro j
            have hrec₁ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₁ kk j
            have hrec₂ :=
              higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU₂ kk j
            have hprefix :
                higham9_2_rectPrefixDot L₁ U₁ kk j kk =
                  higham9_2_rectPrefixDot L₂ U₂ kk j kk := by
              unfold higham9_2_rectPrefixDot
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s.val < kk.val
              · have hp := hprev s hs
                simp [hs, hp.2 kk, hp.1 j]
              · simp [hs]
            rw [hrec₁, hrec₂]
            unfold higham9_2_rectDoolittleUUpdate
            simp [higham9_2_rectRow, hprefix]
          have hU₂diag : U₂ kk kk ≠ 0 := by
            rw [← hUeq kk]
            exact hU₁diag kk
          have hLeq : ∀ i : Fin n, L₁ i kk = L₂ i kk := by
            intro i
            have hrec₁ :=
              higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₁ i kk
                (hU₁diag kk)
            have hrec₂ :=
              higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec hLU₂ i kk
                hU₂diag
            have hprefix :
                higham9_2_rectPrefixDot L₁ U₁ i kk kk =
                  higham9_2_rectPrefixDot L₂ U₂ i kk kk := by
              unfold higham9_2_rectPrefixDot
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s.val < kk.val
              · have hp := hprev s hs
                simp [hs, hp.2 i, hp.1 kk]
              · simp [hs]
            rw [hrec₁, hrec₂]
            unfold higham9_2_rectDoolittleLUpdate
            simp [hprefix, hUeq kk]
          exact ⟨hUeq, hLeq⟩
  constructor
  · funext i j
    exact (hstage n (Nat.le_refl n) j j.isLt).2 i
  · funext i j
    exact (hstage n (Nat.le_refl n) i i.isLt).1 j

/-- **Algorithm 9.2**, printed leading flop-count polynomial
`n^2 (m - n/3)`, represented over `ℚ`.  The rational codomain records the
source expression itself; this declaration is not an exact integer operation
count for a fully specified executable loop. -/
def higham9_2_doolittleSourceFlopPolynomial (m n : ℕ) : ℚ :=
  (n : ℚ) ^ 2 * ((m : ℚ) - (n : ℚ) / 3)

/-- **Algorithm 9.2**, algebraic expansion of the printed leading flop-count
polynomial. -/
theorem higham9_2_doolittleSourceFlopPolynomial_eq (m n : ℕ) :
    higham9_2_doolittleSourceFlopPolynomial m n =
      (m : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ^ 3 / 3 := by
  unfold higham9_2_doolittleSourceFlopPolynomial
  ring

/-- **Algorithm 9.2**, the one-column specialization of the printed cost
expression is rational.  This documents why the source expression is treated as
a leading polynomial rather than as a literal natural-number loop count. -/
theorem higham9_2_doolittleSourceFlopPolynomial_one (m : ℕ) :
    higham9_2_doolittleSourceFlopPolynomial m 1 = (m : ℚ) - 1 / 3 := by
  simp [higham9_2_doolittleSourceFlopPolynomial]

/-- **Equation (9.5)**: finite prefix of the rank-one GE updates, written with
an explicit natural-number step count.  Terms beyond the rectangular column
range contribute zero, so this definition is total in `steps`. -/
noncomputable def higham9_5_rectPrefixRange {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (steps : ℕ) : ℝ :=
  ∑ r ∈ Finset.range steps,
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0

/-- **Equation (9.5)**: the reduced matrix entry obtained from the original
entry after `steps` exact no-pivot GE rank-one updates. -/
noncomputable def higham9_5_rectGEReducedEntry {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (steps : ℕ) (i : Fin m) (j : Fin n) : ℝ :=
  A i j - higham9_5_rectPrefixRange L U i j steps

/-- **Equation (9.5)** starts from the original matrix before any rank-one
updates. -/
theorem higham9_5_rectGEReducedEntry_zero {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U 0 i j = A i j := by
  simp [higham9_5_rectGEReducedEntry, higham9_5_rectPrefixRange]

/-- **Equation (9.5)** as a one-step exact GE recurrence: moving from `s`
completed updates to `s+1` subtracts the displayed `l_is u_sj` term. -/
theorem higham9_5_rectGEReducedEntry_succ_of_lt {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (steps : ℕ) (hsteps : steps < n) (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U (steps + 1) i j =
      higham9_5_rectGEReducedEntry A L U steps i j -
        L i ⟨steps, hsteps⟩ * U ⟨steps, hsteps⟩ j := by
  unfold higham9_5_rectGEReducedEntry higham9_5_rectPrefixRange
  rw [Finset.sum_range_succ]
  simp [hsteps]
  ring

/-- The natural-number prefix used in equation (9.5) agrees with the masked
`Fin n` prefix used in the source-facing Doolittle recurrences. -/
theorem higham9_5_rectPrefixRange_eq_rectPrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    higham9_5_rectPrefixRange L U i j k.val =
      higham9_2_rectPrefixDot L U i j k := by
  unfold higham9_5_rectPrefixRange higham9_2_rectPrefixDot
  rw [finMaskedPrefixSum_eq_finSum k (fun s : Fin n => L i s * U s j)]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro s _
  have hsn : s.val < n := Nat.lt_trans s.isLt k.isLt
  simp [hsn]

/-- **Equation (9.5)** in closed form: after `k.val` exact GE rank-one updates,
the reduced entry is the original entry minus the Doolittle prefix dot product
through columns/rows preceding `k`. -/
theorem higham9_5_rectGEReducedEntry_eq_rectPrefixDot {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val i j =
      A i j - higham9_2_rectPrefixDot L U i j k := by
  simp [higham9_5_rectGEReducedEntry,
    higham9_5_rectPrefixRange_eq_rectPrefixDot L U i j k]

/-- **Equation (9.5)** specialized to the upper-row Doolittle assignment: the
exact Doolittle upper update is precisely the corresponding no-pivot GE reduced
matrix entry. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate {m n : ℕ}
    (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val
        (higham9_2_rectRow hmn k) j =
      higham9_2_rectDoolittleUUpdate hmn A L U k j := by
  simp [higham9_5_rectGEReducedEntry_eq_rectPrefixDot,
    higham9_2_rectDoolittleUUpdate]

/-- **Equation (9.5)** specialized to the lower-column Doolittle assignment:
the reduced entry is the lower numerator before division by the pivot. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleLNumerator {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) :
    higham9_5_rectGEReducedEntry A L U k.val i k =
      A i k - higham9_2_rectPrefixDot L U i k k := by
  simp [higham9_5_rectGEReducedEntry_eq_rectPrefixDot]

/-- **Equation (9.5)** in the lower-column source orientation: with a nonzero
pivot, the exact GE reduced entry equals `l_ik u_kk` for the Doolittle lower
update. -/
theorem higham9_5_rectGEReducedEntry_eq_DoolittleLUpdate_mul_pivot {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n)
    (hUkk : U k k ≠ 0) :
    higham9_5_rectGEReducedEntry A L U k.val i k =
      higham9_2_rectDoolittleLUpdate A L U i k * U k k := by
  rw [higham9_5_rectGEReducedEntry_eq_DoolittleLNumerator]
  unfold higham9_2_rectDoolittleLUpdate
  rw [div_mul_cancel₀ _ hUkk]

/-- **Equation (9.5) / Algorithm 9.2**, upper-entry reduced residual form of a
rectangular dense-loop certificate. -/
theorem higham9_5_rectDenseLoopCertificate_upper_reduced_residual_compression
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopCertificate hmn A L U fp)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_5_rectGEReducedEntry A L U k.val
        (higham9_2_rectRow hmn k) j - U k j| ≤
      gamma fp n * |U k j| := by
  simpa [higham9_5_rectGEReducedEntry_eq_rectPrefixDot] using
    hC.U_residual_compression k j hkj

/-- **Equation (9.5) / Algorithm 9.2**, lower-entry reduced residual form of a
rectangular dense-loop certificate. -/
theorem higham9_5_rectDenseLoopCertificate_lower_reduced_residual_compression
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopCertificate hmn A L U fp)
    (i : Fin m) (k : Fin n) (hki : k.val < i.val) :
    |higham9_5_rectGEReducedEntry A L U k.val i k -
        L i k * U k k| ≤
      gamma fp n * |L i k * U k k| := by
  simpa [higham9_5_rectGEReducedEntry_eq_rectPrefixDot] using
    hC.L_residual_compression i k hki

/-- **Equation (9.5) / Algorithm 9.2**, upper-entry reduced residual form of a
rectangular absolute-budget certificate. -/
theorem higham9_5_rectAbsBudgetCertificate_upper_reduced_abs_residual
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {BU : Fin n → Fin n → ℝ} {BL : Fin m → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L U fp BU BL)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_5_rectGEReducedEntry A L U k.val
        (higham9_2_rectRow hmn k) j - U k j| ≤
      BU k j := by
  simpa [higham9_5_rectGEReducedEntry_eq_rectPrefixDot] using
    hC.U_abs_residual k j hkj

/-- **Equation (9.5) / Algorithm 9.2**, lower-entry reduced residual form of a
rectangular absolute-budget certificate. -/
theorem higham9_5_rectAbsBudgetCertificate_lower_reduced_abs_residual
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {BU : Fin n → Fin n → ℝ} {BL : Fin m → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L U fp BU BL)
    (i : Fin m) (k : Fin n) (hki : k.val < i.val) :
    |higham9_5_rectGEReducedEntry A L U k.val i k -
        L i k * U k k| ≤
      BL i k := by
  simpa [higham9_5_rectGEReducedEntry_eq_rectPrefixDot] using
    hC.L_abs_residual i k hki

/-- **Equation (9.5) / Algorithm 9.2**, upper-entry reduced residual
compression obtained from a rectangular absolute-budget certificate. -/
theorem higham9_5_rectAbsBudgetCertificate_upper_reduced_residual_compression
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {BU : Fin n → Fin n → ℝ} {BL : Fin m → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L U fp BU BL)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_5_rectGEReducedEntry A L U k.val
        (higham9_2_rectRow hmn k) j - U k j| ≤
      gamma fp n * |U k j| :=
  higham9_5_rectDenseLoopCertificate_upper_reduced_residual_compression
    (higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate hC)
    k j hkj

/-- **Equation (9.5) / Algorithm 9.2**, lower-entry reduced residual
compression obtained from a rectangular absolute-budget certificate. -/
theorem higham9_5_rectAbsBudgetCertificate_lower_reduced_residual_compression
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {BU : Fin n → Fin n → ℝ} {BL : Fin m → Fin n → ℝ}
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L U fp BU BL)
    (i : Fin m) (k : Fin n) (hki : k.val < i.val) :
    |higham9_5_rectGEReducedEntry A L U k.val i k -
        L i k * U k k| ≤
      gamma fp n * |L i k * U k k| :=
  higham9_5_rectDenseLoopCertificate_lower_reduced_residual_compression
    (higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate hC)
    i k hki

/-- **Equation (9.5) / Algorithm 9.2**, upper-entry reduced residual
compression for the concrete rectangular rounded loop under explicit nonzero
pivot and budget-dominance hypotheses. -/
theorem higham9_5_rectRoundedLoop_upper_reduced_residual_compression
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp hmn A i k *
            higham9_2_rectRoundedLoopU fp hmn A k k|)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_5_rectGEReducedEntry A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A) k.val
        (higham9_2_rectRow hmn k) j -
      higham9_2_rectRoundedLoopU fp hmn A k j| ≤
      gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j| :=
  higham9_5_rectAbsBudgetCertificate_upper_reduced_residual_compression
    (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate
      fp hmn A hU_diag hn hU_budget_le hL_budget_le)
    k j hkj

/-- **Equation (9.5) / Algorithm 9.2**, lower-entry reduced residual
compression for the concrete rectangular rounded loop under explicit nonzero
pivot and budget-dominance hypotheses. -/
theorem higham9_5_rectRoundedLoop_lower_reduced_residual_compression
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp hmn A i k *
            higham9_2_rectRoundedLoopU fp hmn A k k|)
    (i : Fin m) (k : Fin n) (hki : k.val < i.val) :
    |higham9_5_rectGEReducedEntry A
        (higham9_2_rectRoundedLoopL fp hmn A)
        (higham9_2_rectRoundedLoopU fp hmn A) k.val i k -
      higham9_2_rectRoundedLoopL fp hmn A i k *
        higham9_2_rectRoundedLoopU fp hmn A k k| ≤
      gamma fp n *
        |higham9_2_rectRoundedLoopL fp hmn A i k *
          higham9_2_rectRoundedLoopU fp hmn A k k| :=
  higham9_5_rectAbsBudgetCertificate_lower_reduced_residual_compression
    (higham9_2_rectRoundedLoop_to_rectAbsBudgetCertificate
      fp hmn A hU_diag hn hU_budget_le hL_budget_le)
    i k hki

/-- **Theorem 9.3**, Doolittle-certified form:
`L_hat U_hat = A + ΔA`, with `|ΔA| ≤ γ_n |L_hat||U_hat|`. -/
theorem higham9_3_doolittle_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hD : higham9_2_DoolittleLU n A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  doolittle_backward_error n fp A L_hat U_hat hn hD

end NumStability
