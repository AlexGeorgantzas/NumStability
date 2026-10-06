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
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.ActiveSuffix
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Problem04.FactorizationExistence

This module formalizes the source-facing Chapter 13 statements for
`Problem04.FactorizationExistence`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed exact-κ bounds when the Schur complement is identified as a
    lower-right block of the formal growth-factor matrix.

    This removes the direct norm hypothesis
    `||S||_max <= ||U||_max` from
    `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa`
    and replaces it by concrete GE bookkeeping: every entry of the displayed
    Schur complement is the corresponding lower-right entry of `U`. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A U : Fin (r + s) → Fin (r + s) → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hS_block : ∀ i j : Fin s,
      (A22 - A21 * ⅟A11 * A12) i j =
        U (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) * growthFactorEntry hN A U hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        growthFactorEntry hN A U hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  exact
    higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa
      hr hs hN A U A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn
      (maxEntryNormRect_le_maxEntryNorm_of_reindex_eq
        hN hs hs (A22 - A21 * ⅟A11 * A12) U
        (fun i => finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (fun j => finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
        hS_block)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the one-step Schur-stage matrix associated with a two-block partition.

    Its lower-right block is the displayed Schur complement; entries outside
    that lower-right block are retained from `A`.  This is a concrete local
    stage object for the max-entry growth-factor route, not a claim that the
    final upper factor contains every generated Schur-complement entry. -/
noncomputable def higham13_problem13_4_schurStageMatrix {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ) :
    Fin (r + s) → Fin (r + s) → ℝ :=
  fun i j =>
    match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | Sum.inr si, Sum.inr sj => S si sj
    | _, _ => A i j

/-- The lower-right block of
    `higham13_problem13_4_schurStageMatrix` is exactly the supplied Schur
    complement. -/
@[simp] theorem higham13_problem13_4_schurStageMatrix_lower_right {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (S : Matrix (Fin s) (Fin s) ℝ)
    (i j : Fin s) :
    higham13_problem13_4_schurStageMatrix A S
        (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) =
      S i j := by
  simp [higham13_problem13_4_schurStageMatrix]

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-indexed exact-κ bounds for the concrete Schur-stage growth matrix.

    This instantiates the formal growth-factor matrix in
    `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix`
    with the local generated stage whose lower-right block is the Schur
    complement `A22 - A21 A11^{-1} A12`. -/
theorem higham13_problem13_4_maxEntry_bounds_from_source_schurStageMatrix_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ)) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) *
          growthFactorEntry hN A
            (higham13_problem13_4_schurStageMatrix A
              (A22 - A21 * ⅟A11 * A12)) hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) ∧
      maxEntryNormRect hs hs (A22 - A21 * ⅟A11 * A12) *
          maxEntryNormRect hs hs
            ((⅟(A22 - A21 * ⅟A11 * A12)) : Matrix (Fin s) (Fin s) ℝ) ≤
        growthFactorEntry hN A
            (higham13_problem13_4_schurStageMatrix A
              (A22 - A21 * ⅟A11 * A12)) hApos *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  exact
    higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix
      hr hs hN A
      (higham13_problem13_4_schurStageMatrix A (A22 - A21 * ⅟A11 * A12))
      A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn
      (by
        intro i j
        exact (higham13_problem13_4_schurStageMatrix_lower_right A
          (A22 - A21 * ⅟A11 * A12) i j).symm)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 feeding equation (13.22):
    the local Schur-stage lower-block bound has the scalar shape needed for the
    `‖L‖ <= n ρ_n^2 κ(A)` premise once the chosen growth-factor matrix also
    dominates the initial matrix.

    This is intentionally a local-stage premise bridge, not the global recursive
    `L`-factor theorem: the hypothesis `hA_le_stage` records the remaining
    global growth-factor bookkeeping obligation. -/
theorem higham13_problem13_4_L21_eq13_22_premise_from_source_schurStageMatrix_exact_kappa
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < r + s)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin s) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    [Invertible A11] [Invertible (A22 - A21 * ⅟A11 * A12)]
    [Invertible (Matrix.fromBlocks A11 A12 A21 A22)]
    (hA11_block : A11 =
      fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA12_block : A12 =
      fun (i : Fin r) (j : Fin s) =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hApos : 0 < maxEntryNorm hN A)
    (n : ℕ)
    (hsn : (s : ℝ) ≤ (n : ℝ))
    (hA_le_stage :
      maxEntryNorm hN A ≤
        maxEntryNorm hN
          (higham13_problem13_4_schurStageMatrix A
            (A22 - A21 * ⅟A11 * A12))) :
    maxEntryNormRect hs hr ((A21 * ⅟A11 : Matrix (Fin s) (Fin r) ℝ)) ≤
        (n : ℝ) *
          (growthFactorEntry hN A
            (higham13_problem13_4_schurStageMatrix A
              (A22 - A21 * ⅟A11 * A12)) hApos) ^ 2 *
          (maxEntryNormRect hN hN A *
            maxEntryNormRect hN hN (nonsingInv (r + s) A)) := by
  let U : Fin (r + s) → Fin (r + s) → ℝ :=
    higham13_problem13_4_schurStageMatrix A (A22 - A21 * ⅟A11 * A12)
  exact
    higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa
      hr hs hN A U A11 A12 A21 A22
      hA11_block hA12_block hA21_block hA22_block
      hApos n hsn hA_le_stage
      (maxEntryNormRect_le_maxEntryNorm_of_reindex_eq
        hN hs hs (A22 - A21 * ⅟A11 * A12) U
        (fun i => finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (fun j => finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
        (by
          intro i j
          exact (higham13_problem13_4_schurStageMatrix_lower_right A
            (A22 - A21 * ⅟A11 * A12) i j).symm))

/-- Higham, 2nd ed., Chapter 13, Problem 13.4: every canonical active-suffix
    first pivot is nonsingular when the Algorithm 13.3 pivot table consists
    of exact right inverses. -/
theorem higham13_problem13_4_activeSuffix_A11_det_ne_zero_of_pivot_right_inverse
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            q hkq)) ≠ 0 := by
  intro q k hkq
  have hkM : k < M := by omega
  have hpivot :=
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse_at
      A pivotInv k hkM (hPivotRight k hkM)
  simpa [blockMatrixFirstSplitA11,
    higham13_algorithm13_3_activeSuffixStageTailBlock,
    higham13_algorithm13_3_schurStageMatrixTailBlock,
    higham13_algorithm13_3_activeSuffixTail] using hpivot

/-- Higham, 2nd ed., Chapter 13, Problem 13.4: the supplied active-stage
    right inverse is the canonical inverse of the corresponding suffix pivot. -/
theorem higham13_problem13_4_activeSuffix_pivot_eq_invOf_of_pivot_right_inverse
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            q hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            q hkq)) := by
  intro q k hkq _
  have hkM : k < M := by omega
  apply matrix_invOf_eq_of_isRightInverse
  intro i j
  simpa [blockMatrixFirstSplitA11,
    higham13_algorithm13_3_activeSuffixStageTailBlock,
    higham13_algorithm13_3_schurStageMatrixTailBlock,
    higham13_algorithm13_3_activeSuffixTail] using hPivotRight k hkM i j

/-- Higham, 2nd ed., Chapter 13, Problem 13.4: exact right inverses for the
    active Algorithm 13.3 pivots recursively imply nonsingularity of every
    canonical active-suffix first-split parent matrix. -/
theorem higham13_problem13_4_activeSuffix_fromBlocks_det_ne_zero_of_pivot_right_inverse
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) ≠ 0 := by
  intro q
  induction q with
  | zero =>
      intro k hkq
      let Tail :=
        higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k 0 hkq
      have hA11det : Matrix.det (blockMatrixFirstSplitA11 Tail) ≠ 0 := by
        simpa [Tail] using
          higham13_problem13_4_activeSuffix_A11_det_ne_zero_of_pivot_right_inverse A pivotInv hPivotRight hkq
      letI : Invertible (Matrix.det (blockMatrixFirstSplitA11 Tail)) :=
        invertibleOfNonzero hA11det
      letI : Invertible (blockMatrixFirstSplitA11 Tail) :=
        Matrix.invertibleOfDetInvertible _
      rw [Matrix.det_fromBlocks₁₁]
      apply mul_ne_zero hA11det
      letI : IsEmpty (Fin (0 * r)) := ⟨fun i => by simpa using i.isLt⟩
      rw [Matrix.det_isEmpty]
      norm_num
  | succ q ih =>
      intro k hkq
      have hkM : k < M := by omega
      have htail : k + 1 + (q + 1) ≤ M := by omega
      let Tail :=
        higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
          (q + 1) hkq
      let Next :=
        higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv (k + 1)
          q htail
      have hA11det : Matrix.det (blockMatrixFirstSplitA11 Tail) ≠ 0 := by
        simpa [Tail] using
          higham13_problem13_4_activeSuffix_A11_det_ne_zero_of_pivot_right_inverse A pivotInv hPivotRight hkq
      letI : Invertible (Matrix.det (blockMatrixFirstSplitA11 Tail)) :=
        invertibleOfNonzero hA11det
      letI : Invertible (blockMatrixFirstSplitA11 Tail) :=
        Matrix.invertibleOfDetInvertible _
      have hpivot : pivotInv k = ⅟(blockMatrixFirstSplitA11 Tail) := by
        simpa [Tail] using
          higham13_problem13_4_activeSuffix_pivot_eq_invOf_of_pivot_right_inverse A pivotInv hPivotRight hkq
      have hNextDet : Matrix.det (Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Next)
          (blockMatrixFirstSplitA12 Next)
          (blockMatrixFirstSplitA21 Next)
          (blockMatrixFirstSplitA22 Next)) ≠ 0 := by
        simpa [Next] using ih htail
      have hNextFlatDet : Matrix.det (blockMatrixFlatFin Next) ≠ 0 := by
        rw [← det_blockMatrixFirstSplit_fromBlocks_eq_blockMatrixFlatFin Next]
        exact hNextDet
      letI : Invertible (Matrix.det (blockMatrixFlatFin Next)) :=
        invertibleOfNonzero hNextFlatDet
      letI : Invertible (blockMatrixFlatFin Next) :=
        Matrix.invertibleOfDetInvertible _
      have hSchurEq :
          blockMatrixFirstSplitA22 Tail -
              blockMatrixFirstSplitA21 Tail *
                ⅟(blockMatrixFirstSplitA11 Tail) *
                  blockMatrixFirstSplitA12 Tail =
            blockMatrixFlatFin Next := by
        rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur]
        have hStep :=
          higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
            A pivotInv hkM
            (higham13_algorithm13_3_activeSuffixTail M k ((q + 1) + 1) hkq)
            (higham13_algorithm13_3_activeSuffixTail M (k + 1) (q + 1) htail)
            (higham13_algorithm13_3_activeSuffixTail_zero hkq hkM)
            (fun i => higham13_algorithm13_3_activeSuffixTail_succ hkq htail i)
            (fun i => higham13_algorithm13_3_activeSuffixTail_active htail i)
        rw [← hpivot]
        exact congrArg blockMatrixFlatFin (by
          simpa [Tail, Next,
            higham13_algorithm13_3_activeSuffixStageTailBlock] using hStep)
      letI : Invertible
          (blockMatrixFirstSplitA22 Tail -
            blockMatrixFirstSplitA21 Tail *
              ⅟(blockMatrixFirstSplitA11 Tail) *
                blockMatrixFirstSplitA12 Tail) :=
        Invertible.copy (inferInstance : Invertible (blockMatrixFlatFin Next))
          _ hSchurEq
      letI : Invertible (Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Tail)
          (blockMatrixFirstSplitA12 Tail)
          (blockMatrixFirstSplitA21 Tail)
          (blockMatrixFirstSplitA22 Tail)) :=
        Matrix.fromBlocks₁₁Invertible _ _ _ _
      letI : Invertible (Matrix.det (Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Tail)
          (blockMatrixFirstSplitA12 Tail)
          (blockMatrixFirstSplitA21 Tail)
          (blockMatrixFirstSplitA22 Tail))) :=
        Matrix.detInvertibleOfInvertible _
      simpa [Tail] using Invertible.ne_zero (Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 Tail)
        (blockMatrixFirstSplitA12 Tail)
        (blockMatrixFirstSplitA21 Tail)
        (blockMatrixFirstSplitA22 Tail)))

/-- The canonical `Invertible` witness for an active-suffix first pivot,
    constructed from the Algorithm 13.3 right-inverse table. -/
noncomputable def higham13_problem13_4_activeSuffix_A11_invertible_of_pivot_right_inverse
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    {q k : ℕ} (hkq : k + (q + 1) ≤ M) :
    Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq)) := by
  let A11 := blockMatrixFirstSplitA11
    (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq)
  letI : Invertible (Matrix.det A11) := invertibleOfNonzero (by
    simpa [A11] using
      higham13_problem13_4_activeSuffix_A11_det_ne_zero_of_pivot_right_inverse A pivotInv hPivotRight hkq)
  exact Matrix.invertibleOfDetInvertible A11

/-- The canonical `Invertible` witness for an active-suffix Schur complement,
    obtained from nonsingularity of the next recursively generated suffix. -/
noncomputable def higham13_problem13_4_activeSuffix_schur_invertible_of_pivot_right_inverse
    {M r : ℕ}
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
          (q + 1) hkq))] :
    Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
              (q + 1) hkq) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                (q + 1) hkq)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                (q + 1) hkq)) := by
  classical
  have hkM : k < M := by omega
  have htail : k + 1 + (q + 1) ≤ M := by omega
  let Tail :=
    higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
      (q + 1) hkq
  let Next :=
    higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv (k + 1)
      q htail
  have hpivot : pivotInv k = ⅟(blockMatrixFirstSplitA11 Tail) := by
    simpa [Tail] using
      higham13_problem13_4_activeSuffix_pivot_eq_invOf_of_pivot_right_inverse A pivotInv hPivotRight hkq
  have hNextFromBlocksDet : Matrix.det (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Next)
      (blockMatrixFirstSplitA12 Next)
      (blockMatrixFirstSplitA21 Next)
      (blockMatrixFirstSplitA22 Next)) ≠ 0 := by
    simpa [Next] using
      higham13_problem13_4_activeSuffix_fromBlocks_det_ne_zero_of_pivot_right_inverse A pivotInv hPivotRight htail
  have hNextFlatDet : Matrix.det (blockMatrixFlatFin Next) ≠ 0 := by
    rw [← det_blockMatrixFirstSplit_fromBlocks_eq_blockMatrixFlatFin Next]
    exact hNextFromBlocksDet
  letI : Invertible (Matrix.det (blockMatrixFlatFin Next)) :=
    invertibleOfNonzero hNextFlatDet
  letI : Invertible (blockMatrixFlatFin Next) :=
    Matrix.invertibleOfDetInvertible _
  have hSchurEq :
      blockMatrixFirstSplitA22 Tail -
          blockMatrixFirstSplitA21 Tail *
            ⅟(blockMatrixFirstSplitA11 Tail) *
              blockMatrixFirstSplitA12 Tail =
        blockMatrixFlatFin Next := by
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur]
    have hStep :=
      higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
        A pivotInv hkM
        (higham13_algorithm13_3_activeSuffixTail M k ((q + 1) + 1) hkq)
        (higham13_algorithm13_3_activeSuffixTail M (k + 1) (q + 1) htail)
        (higham13_algorithm13_3_activeSuffixTail_zero hkq hkM)
        (fun i => higham13_algorithm13_3_activeSuffixTail_succ hkq htail i)
        (fun i => higham13_algorithm13_3_activeSuffixTail_active htail i)
    rw [← hpivot]
    exact congrArg blockMatrixFlatFin (by
      simpa [Tail, Next,
        higham13_algorithm13_3_activeSuffixStageTailBlock] using hStep)
  exact Invertible.copy
    (inferInstance : Invertible (blockMatrixFlatFin Next)) _ hSchurEq

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 and equation (13.22): for a
    matrix with at least two blocks, one exact Algorithm 13.3 pivot table
    supplies every recursive parent/suffix inverse obligation and yields the
    exact source `n * rho^3 * kappa(A) * ‖A‖` product bound. -/
theorem higham13_problem13_4_eq13_22_exists_blockLUFact_succ_of_pivot_right_inverse
    {m r n : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hdet : Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r A L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
              (blockMatrixFirstSplitFlat A)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.succ_pos (m + 1)) hr A pivotInv)
              (maxEntryNorm_pos_of_det_ne_zero
                (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A) hdet)) ^ 3 *
            (maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A) *
              maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat A))) *
            maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
              (Nat.add_pos_left hr ((m + 1) * r))
              (blockMatrixFirstSplitFlat A) := by
  classical
  let hN : 0 < r + (m + 1) * r := Nat.add_pos_left hr ((m + 1) * r)
  have hfull : 0 + (((m + 1) + 1)) ≤ (m + 1) + 1 := by omega
  let hInvA11 : ∀ {q k : ℕ}
      (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    exact higham13_problem13_4_activeSuffix_A11_invertible_of_pivot_right_inverse A pivotInv hPivotRight hkq
  let hInvSchur : ∀ {q k : ℕ}
      (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
              (q + 1) hkq) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                (q + 1) hkq) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (q + 1) hkq)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (q + 1) hkq)) := by
    intro q k hkq
    letI := hInvA11 hkq
    exact higham13_problem13_4_activeSuffix_schur_invertible_of_pivot_right_inverse A pivotInv hPivotRight hkq
  let hpivotAll : ∀ {q k : ℕ}
      (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    letI := hInvA11 hkq
    exact higham13_problem13_4_activeSuffix_pivot_eq_invOf_of_pivot_right_inverse A pivotInv hPivotRight hkq
  letI : Invertible (blockMatrixFirstSplitA11 A) := by
    simpa [higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq A pivotInv
      hfull] using hInvA11 (q := m) (k := 0) hfull
  letI : Invertible
      (blockMatrixFirstSplitA22 A -
        blockMatrixFirstSplitA21 A * ⅟(blockMatrixFirstSplitA11 A) *
          blockMatrixFirstSplitA12 A) := by
    simpa [higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq A pivotInv
      hfull] using hInvSchur (q := m) (k := 0) hfull
  have hFullFromBlocksDet : Matrix.det (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)) ≠ 0 := by
    simpa [higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq A pivotInv
      hfull] using
        higham13_problem13_4_activeSuffix_fromBlocks_det_ne_zero_of_pivot_right_inverse A pivotInv hPivotRight hfull
  letI : Invertible (Matrix.det (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A))) :=
    invertibleOfNonzero hFullFromBlocksDet
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)) :=
    Matrix.invertibleOfDetInvertible _
  have hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 A) := by
    simpa [higham13_algorithm13_3_activeSuffixStageTailBlock_zero_eq A pivotInv
      hfull] using hpivotAll (q := m) (k := 0) hfull
  have hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hNat : (m + 1) * r ≤ ((m + 1) + 1) * r :=
      Nat.mul_le_mul_right r (by omega)
    exact le_trans (by exact_mod_cast hNat) hFulln
  have hNn : ((r + (m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hdim : r + (m + 1) * r = ((m + 1) + 1) * r := by
      simp [Nat.add_mul, Nat.add_comm]
    rw [hdim]
    exact hFulln
  have hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ) := by
    intro q k hkq
    exact higham13_activeSuffix_dimension_budget_of_global_bound hFulln hkq
  simpa [hN] using
    higham13_eq13_22_exists_blockLUFact_succ_product_from_global_tableau_activeSuffix_matrix_stage_history_exact_kappa_of_canonical_parent_inverse_entry_of_det_ne_zero
      hr hN A pivotInv hpivot
      (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat A) hdet)
      hdet hsn hNn hsnAll hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, equation (13.23): specializing the parent-local
    Eq.13.22 factor witness by the source growth estimate `rho <= 2` gives the
    point-row constant `8`. -/
theorem higham13_problem13_4_eq13_23_exists_blockLUFact_succ_of_pivot_right_inverse
    {m r n : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hdet : Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0)
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hRho_le_two :
      growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
          (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            (Nat.add_pos_left hr ((m + 1) * r))
            (Nat.succ_pos (m + 1)) hr A pivotInv)
          (maxEntryNorm_pos_of_det_ne_zero
            (Nat.add_pos_left hr ((m + 1) * r))
            (blockMatrixFirstSplitFlat A) hdet) ≤
        2) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r A L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A) *
              maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (nonsingInv (r + (m + 1) * r)
                  (blockMatrixFirstSplitFlat A))) *
            maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
              (Nat.add_pos_left hr ((m + 1) * r))
              (blockMatrixFirstSplitFlat A) := by
  rcases higham13_problem13_4_eq13_22_exists_blockLUFact_succ_of_pivot_right_inverse
      hr A pivotInv hPivotRight hdet hFulln with ⟨L, U, hLU, h22⟩
  refine ⟨L, U, hLU, le_trans h22 ?_⟩
  let hN : 0 < r + (m + 1) * r := Nat.add_pos_left hr ((m + 1) * r)
  let rho := growthFactorEntry hN (blockMatrixFirstSplitFlat A)
    (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
      hN (Nat.succ_pos (m + 1)) hr A pivotInv)
    (maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat A) hdet)
  let kappa :=
    maxEntryNormRect hN hN (blockMatrixFirstSplitFlat A) *
      maxEntryNormRect hN hN
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
  let normA := maxEntryNormRect hN hN (blockMatrixFirstSplitFlat A)
  have hrho_nonneg : 0 ≤ rho := by
    exact growthFactorEntry_nonneg hN _ _ _
  have hrho_le_two : rho ≤ 2 := by
    simpa [rho, hN] using hRho_le_two
  have hrho3 : rho ^ 3 ≤ 8 := by
    have hpow : rho ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hrho_nonneg hrho_le_two 3
    norm_num at hpow
    exact hpow
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkappa : 0 ≤ kappa := by
    exact mul_nonneg
      (maxEntryNormRect_nonneg hN hN (blockMatrixFirstSplitFlat A))
      (maxEntryNormRect_nonneg hN hN
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A)))
  have hnormA : 0 ≤ normA :=
    maxEntryNormRect_nonneg hN hN (blockMatrixFirstSplitFlat A)
  have hcoef :
      (n : ℝ) * rho ^ 3 * kappa * normA ≤
        (n : ℝ) * 8 * kappa * normA := by
    gcongr
  simpa [hN, rho, kappa, normA] using
    (show (n : ℝ) * rho ^ 3 * kappa * normA ≤
        8 * (n : ℝ) * kappa * normA by
      calc
        (n : ℝ) * rho ^ 3 * kappa * normA ≤
            (n : ℝ) * 8 * kappa * normA := hcoef
        _ = 8 * (n : ℝ) * kappa * normA := by ring)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3, Problem 13.4, and equation
    (13.23): all-leading-prefix nonsingularity constructs the single recursive
    pivot table, while ordinary block column diagonal dominance supplies the
    dimension-free growth estimate.  No all-tail inverse table is required. -/
theorem
    higham13_problem13_4_exists_pivotInv_eq13_23_succ_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm
    {m r n : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (hDiagDet : ∀ j : Fin ((m + 1) + 1), Matrix.det (A j j) ≠ 0)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDom : IsBlockDiagDomCol ((m + 1) + 1)
      (fun i j : Fin ((m + 1) + 1) => infNorm (A i j))
      (fun j : Fin ((m + 1) + 1) =>
        (infNorm (nonsingInv r (A j j)))⁻¹))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
          Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r A L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                  (Nat.add_pos_left hr ((m + 1) * r))
                  (blockMatrixFirstSplitFlat A) *
                maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                  (Nat.add_pos_left hr ((m + 1) * r))
                  (nonsingInv (r + (m + 1) * r)
                    (blockMatrixFirstSplitFlat A))) *
              maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A) := by
  classical
  let hm : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < r + (m + 1) * r := Nat.add_pos_left hr ((m + 1) * r)
  let hFlat : 0 < ((m + 1) + 1) * r := Nat.mul_pos hm hr
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_all_leadingBlockPrefixes
        A hPrefix with ⟨pivotInv, hPivotRight⟩
  have hFlatDet : Matrix.det (blockMatrixFlatFin A) ≠ 0 :=
    higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
      hm (fun i j a b => A i j a b) hPrefix
  have hdet : Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hFlatDet
  have hFlatPos : 0 < maxEntryNorm hFlat (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hFlatDet
  have hSplitPos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat A) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFirstSplitFlat A) hdet
  have hDiagRight : ∀ j : Fin ((m + 1) + 1),
      IsRightInverse r (A j j) (nonsingInv r (A j j)) := by
    intro j
    exact (isInverse_nonsingInv_of_det_ne_zero r (A j j) (hDiagDet j)).2
  have hSource :=
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_initial_diag_right_inverse_of_pivot_right_inverse_mixed_column_mass
      hm hr A pivotInv hFlatPos
      (fun j : Fin ((m + 1) + 1) =>
        (infNorm (nonsingInv r (A j j)))⁻¹)
      (fun j : Fin ((m + 1) + 1) => nonsingInv r (A j j))
      hDom (fun _ => le_rfl) hDiagRight hPivotRight
  have hRhoSplit :
      growthFactorEntry hN (blockMatrixFirstSplitFlat A)
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN hm hr A pivotInv) hSplitPos ≤
        2 := by
    have hEq :=
      growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
        hmTail hr A pivotInv hSplitPos hFlatPos
    rw [hEq]
    exact hSource.2
  refine ⟨pivotInv, hPivotRight, ?_⟩
  simpa [hm, hN] using
    higham13_problem13_4_eq13_23_exists_blockLUFact_succ_of_pivot_right_inverse
      hr A pivotInv hPivotRight hdet hFulln hRhoSplit

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 and equation (13.22):
    all-leading-prefix nonsingularity constructs the Algorithm 13.3 pivot table
    and, through the parent-local recursion, produces the exact source product
    bound for every matrix with at least two blocks. -/
theorem
    higham13_problem13_4_exists_pivotInv_eq13_22_succ_of_all_leadingBlockPrefixes
    {m r n : ℕ} (hr : 0 < r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < (m + 1) + 1,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < (m + 1) + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
          Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec ((m + 1) + 1) r A L U ∧
          blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
              blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
            (n : ℝ) *
              (growthFactorEntry (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A)
                (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                  (Nat.add_pos_left hr ((m + 1) * r))
                  (Nat.succ_pos (m + 1)) hr A pivotInv)
                (maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes
                  (Nat.add_pos_left hr ((m + 1) * r)) A hPrefix)) ^ 3 *
              (maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                  (Nat.add_pos_left hr ((m + 1) * r))
                  (blockMatrixFirstSplitFlat A) *
                maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                  (Nat.add_pos_left hr ((m + 1) * r))
                  (nonsingInv (r + (m + 1) * r)
                    (blockMatrixFirstSplitFlat A))) *
              maxEntryNormRect (Nat.add_pos_left hr ((m + 1) * r))
                (Nat.add_pos_left hr ((m + 1) * r))
                (blockMatrixFirstSplitFlat A) := by
  let hm : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_all_leadingBlockPrefixes
        A hPrefix with ⟨pivotInv, hPivotRight⟩
  have hFlatDet : Matrix.det (blockMatrixFlatFin A) ≠ 0 :=
    higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
      hm (fun i j a b => A i j a b) hPrefix
  have hdet : Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + (m + 1) * r)) (Fin (r + (m + 1) * r)) ℝ) ≠ 0 :=
    det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hFlatDet
  refine ⟨pivotInv, hPivotRight, ?_⟩
  simpa using
    higham13_problem13_4_eq13_22_exists_blockLUFact_succ_of_pivot_right_inverse
      hr A pivotInv hPivotRight hdet hFulln

end NumStability
