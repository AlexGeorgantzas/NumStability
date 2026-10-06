import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.LowerComparisonChain

This module formalizes the source-facing Chapter 13 statements for
`Problem04.LowerComparisonChain`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    recursive source certificate for the direct lower-budget route.

    This predicate records the per-Schur-tail data that remains mathematical:
    determinant nonsingularity, pivot identification, and the direct lower
    budget comparison.  It does not assume the target ambient budget chain. -/
inductive Higham13Eq1322LowerComparisonSourceChain {r : ℕ} (hr : 0 < r)
    (n : ℕ) :
    (m : ℕ) →
      (Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) →
      (ℕ → Matrix (Fin r) (Fin r) ℝ) → Prop
  | one {Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hdet :
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
      (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
      Higham13Eq1322LowerComparisonSourceChain hr n 0 Ablk pivotInv
  | succ {m : ℕ}
      {Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      [Invertible (blockMatrixFirstSplitA11 Ablk)]
      [Invertible (blockMatrixFirstSplitA22 Ablk -
        blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
          blockMatrixFirstSplitA12 Ablk)]
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 Ablk)
        (blockMatrixFirstSplitA12 Ablk)
        (blockMatrixFirstSplitA21 Ablk)
        (blockMatrixFirstSplitA22 Ablk))]
      (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
      (hdetFlat :
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
      (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
      (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
      (let hmTail : 0 < m + 1 := Nat.succ_pos m
       let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
       let hNSplit : 0 < r + (m + 1) * r :=
        Nat.add_pos_left hr ((m + 1) * r)
       let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
       let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
       let Gtail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hNTail hmTail hr (blockSchur Ablk (pivotInv 0))
          (fun q => pivotInv (q + 1))
       let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) Atail
       let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        blockMatrixFirstSplitFlat Ablk
       let GSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hNSplit hmFull hr Ablk pivotInv
       let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        nonsingInv (r + (m + 1) * r) ASplit
       let hTailPos : 0 < maxEntryNorm hNTail Atail :=
        maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
          hr Ablk pivotInv hpivot
       let hApos :
          0 < maxEntryNorm (Nat.mul_pos hmFull hr) (blockMatrixFlatFin Ablk) :=
        maxEntryNorm_pos_of_det_ne_zero (Nat.mul_pos hmFull hr)
          (blockMatrixFlatFin Ablk) hdetFlat
       let hSplitPos : 0 < maxEntryNorm hNSplit ASplit := by
        rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin hmTail hr Ablk]
        exact hApos
       (n : ℝ) * (growthFactorEntry hNTail Atail Gtail hTailPos) ^ 2 *
            (maxEntryNormRect hNTail hNTail Atail *
              maxEntryNormRect hNTail hNTail AinvTail) ≤
          (n : ℝ) * (growthFactorEntry hNSplit ASplit GSplit hSplitPos) ^ 2 *
            (maxEntryNormRect hNSplit hNSplit ASplit *
              maxEntryNormRect hNSplit hNSplit AinvSplit)) →
      Higham13Eq1322LowerComparisonSourceChain hr n m
        (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13Eq1322LowerComparisonSourceChain hr n (m + 1) Ablk pivotInv

/-- The source-chain certificate carries determinant nonsingularity for its
    current block matrix. -/
theorem Higham13Eq1322LowerComparisonSourceChain.det_ne_zero {r n : ℕ}
    {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv) →
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 := by
  intro m Ablk pivotInv hcert
  cases hcert with
  | one hdet _ =>
      simpa using hdet
  | succ _ hdetFlat _ _ _ _ =>
      simpa using hdetFlat

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot right-inverse data carried by the recursive
    direct lower-comparison source certificate.

    The source certificate stores a pivot identity at each genuine elimination
    step.  The one-block base case intentionally carries no condition on
    `pivotInv 0`, since no further elimination step uses it; therefore this
    extractor is stated for `k < m` when the current chain has `m + 1` block
    rows. -/
theorem Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩)
            (pivotInv k) := by
  intro m Ablk pivotInv hcert
  induction hcert with
  | one hdet hNn =>
      intro k hk
      exact (Nat.not_lt_zero k hk).elim
  | @succ m Ablk pivotInv hA11 hSchur hFull hpivot hdetFlat hsn hNn hLower hTail ih =>
      intro k hk
      cases k with
      | zero =>
          letI : Invertible (blockMatrixFirstSplitA11 Ablk) := hA11
          have hri :
              IsRightInverse r (blockMatrixFirstSplitA11 Ablk) (pivotInv 0) :=
            isRightInverse_of_eq_invOf
              (blockMatrixFirstSplitA11 Ablk) (pivotInv 0) hpivot
          simpa [higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock, blockMatrixFirstSplitA11]
            using hri
      | succ k =>
          have hkTail : k < m := Nat.succ_lt_succ_iff.mp hk
          have htail := ih k hkTail
          have hkTailFin : k < m + 1 := Nat.lt_trans hkTail (Nat.lt_succ_self m)
          have hkFull : k + 1 < (m + 1) + 1 :=
            Nat.lt_trans hk (Nat.lt_succ_self (m + 1))
          have hidx :
              (Fin.succ (⟨k, hkTailFin⟩ : Fin (m + 1)) :
                  Fin ((m + 1) + 1)) =
                (⟨k + 1, hkFull⟩ : Fin ((m + 1) + 1)) := by
            ext
            rfl
          have hstage :=
            higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
              Ablk pivotInv k (⟨k, hkTailFin⟩ : Fin (m + 1))
              (⟨k, hkTailFin⟩ : Fin (m + 1))
          simpa [hidx, hstage] using htail

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    determinant nonsingularity of every nonterminal active pivot represented by
    a direct lower-comparison source chain.

    This is the determinant form of
    `Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse`.
    The one-block terminal case is intentionally not included, since the source
    chain records no pivot identity there. -/
theorem Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_det_ne_zero
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          Matrix.det
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert k hk
  have hRight :=
    Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse
      hcert k hk
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
        ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
        ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩)
      (B := pivotInv k)
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot right-inverse table for a direct lower-comparison source
    chain, once the final one-block pivot is supplied separately.

    The recursive source certificate supplies exactly the genuine elimination
    pivots `k < m`.  Some downstream matrix-stage APIs are stated for all
    `k < m + 1`; this wrapper isolates the only additional datum they need:
    the terminal pivot certificate. -/
theorem Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hfinal k hk
  by_cases hkm : k < m
  · exact
      Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse
        hcert k hkm
  · have hle : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have hEq : k = m := Nat.le_antisymm hle hmk
    subst k
    simpa using hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a direct lower-comparison source
    chain, once the final one-block pivot determinant is supplied separately.

    The recursive source certificate supplies determinant nonsingularity for
    all genuine elimination pivots `k < m`; this wrapper isolates the only
    extra datum needed for all-pivot APIs, namely the terminal pivot
    determinant. -/
theorem Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal k hk
  by_cases hkm : k < m
  · exact
      Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_det_ne_zero
        hcert k hkm
  · have hle : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have hEq : k = m := Nat.le_antisymm hle hmk
    subst k
    simpa using hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a direct lower-comparison source
    chain, when the final one-block pivot is supplied as a right-inverse
    certificate.

    This is the right-inverse input surface corresponding to
    `Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final`. -/
theorem Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
      Ablk pivotInv
      (Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final
        hcert hfinal)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot right-inverse table for a direct lower-comparison source chain
    when the terminal one-block pivot is the canonical `nonsingInv`.

    This specializes `pivot_right_inverse_of_final` to the common source data:
    the final stage determinant is nonzero and `pivotInv m` is chosen as
    `nonsingInv` of that final stage block. -/
theorem Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  apply Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final hcert
  simpa [hfinalEq] using
    (isInverse_nonsingInv_of_det_ne_zero r
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
        ⟨m, Nat.lt_succ_self m⟩
        ⟨m, Nat.lt_succ_self m⟩) hdet).2

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot determinant table for a direct lower-comparison source chain
    when the terminal one-block pivot is the canonical `nonsingInv`.

    This is the determinant-table companion to
    `Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv`. -/
theorem Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
      Ablk pivotInv
      (Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv
        hcert hdet hfinalEq)

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    a direct lower-comparison source chain, plus the terminal pivot
    right-inverse certificate, supplies the mixed matrix-`∞`/max-entry
    upper-factor and finite-history growth-factor endpoint.

    The source chain provides the full determinant and all nonterminal pivot
    certificates; this wrapper isolates the only remaining terminal pivot datum
    needed by the mixed source endpoint. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinal
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final
      hcert hFinal
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the direct lower-comparison source-chain
    mixed matrix-`∞`/max-entry endpoint. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv) →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinalDet
    hFinalEq
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv
      hcert hFinalDet hFinalEq
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    a recursive direct-lower-comparison source certificate instantiates the
    ambient exact-κ budget chain.

    This closes the structural recursion/lift part of the Problem 13.4 route:
    the theorem no longer assumes a `Higham13BlockLUBudgetChain`; it builds one
    from per-tail determinant, pivot, and direct lower-budget comparison data.
    The direct lower comparison itself remains the visible mathematical source
    obligation at each recursive Schur tail. -/
theorem Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert)
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
  intro m Ablk pivotInv hcert
  cases hcert with
  | one hdet hNn =>
      dsimp only
      simpa using
        higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa_of_det_ne_zero
          hr _ pivotInv hdet n hNn
  | succ hpivot hdetFlat hsn hNn hLower hTail =>
      have ih :=
        Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain
          (r := r) (n := n) hr hTail
      dsimp only at ih ⊢
      simpa using
        higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero_of_schur_invertible
          hr _ pivotInv hpivot hdetFlat n hsn hNn hLower ih

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    full recursive Eq.13.22 product witness from the direct-lower-comparison
    source certificate. -/
theorem Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert)
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the direct-lower-comparison
    source certificate plus the remaining source-side `rho <= 2` theorem. -/
theorem Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert)
      growthFactorEntry hN A0 G hApos ≤ 2 →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
                maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro hRho_le_two
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the direct lower-comparison
    source certificate and the mixed matrix-`∞`/max-entry BDD endpoint.

    This packages the existing mixed column-mass theorem as the source-side
    `rho <= 2` input needed by Eq.13.23.  The direct per-tail lower comparison,
    BDD leading-prefix data, and terminal pivot right-inverse remain the visible
    mathematical obligations. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinal
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2 := by
    have hEndpoint :=
      Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
        (r := r) (n := n) (hr := hr) hcert
        invDiagBound hPrefix hDomInf hBound hFinal
    simpa [hm, hN, A0, G, hApos] using hEndpoint.2
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) (n := n) hr hcert hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    canonical-terminal-pivot form of
    `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass`.

    The final pivot is supplied as the canonical `nonsingInv`; all other pivot
    certificates and the `rho <= 2` endpoint are derived from the source chain
    and BDD leading-prefix data. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq
  let hFinalRight :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) := by
    simpa [hFinalEq] using
      (isInverse_nonsingInv_of_det_ne_zero r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) hFinalDet).2
  exact
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) hr hcert
      invDiagBound hPrefix hDomInf hBound hFinalRight

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the direct-lower-comparison
    source certificate, with the `rho <= 2` side condition supplied by the
    matrix-stage product-bound/diagonal-update BDD route.

    This removes the raw growth-factor hypothesis from the recursive
    source-chain surface while keeping the source-strength structured
    triple-product estimate and diagonal-update table explicit.  The per-tail
    direct lower comparison and the product-bound/diagonal-update hypotheses
    remain the visible mathematical obligations. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      (∀ k : ℕ, ∀ hk : k < m + 1,
        maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322LowerComparisonSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  exact
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) (n := n) hr hcert
      (by
        simpa [hm, hN, A0, G, Ainv, hApos] using
          higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
            hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
            hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the direct lower-comparison source-chain
    point-row product witness.

    This wrapper keeps the source table in its natural reciprocal form and
    derives the raw pivot product bound internally before invoking the existing
    product-bound/diagonal-update surface. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` BDD form of the direct lower-comparison source-chain
    product/update witness.

    This is the source-norm variant of
    `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update`.
    It derives the max-entry BDD premise internally and keeps the direct
    lower-budget comparisons, structured product estimate, and diagonal-update
    table as the explicit source obligations. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      (∀ k : ℕ, ∀ hk : k < m + 1,
        maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDomInf hBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  exact
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/matrix-`∞` BDD form of the direct lower-comparison
    source-chain product/update witness. -/
theorem
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDomInf hBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hReciprocal hProduct hDiagUpdate

end NumStability
