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
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.InverseRatioChain

This module formalizes the source-facing Chapter 13 statements for
`Problem04.InverseRatioChain`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    recursive source certificate for the inverse-ratio route.

    This is the source-chain version of the optional inverse-ratio transport:
    each Schur-tail step records determinant nonsingularity, the pivot
    identification, and the cross-multiplied inverse-ratio comparison.  The
    ambient budget chain is then built by recursion, rather than assumed. -/
inductive Higham13Eq1322InverseRatioSourceChain {r : ℕ} (hr : 0 < r)
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
      Higham13Eq1322InverseRatioSourceChain hr n 0 Ablk pivotInv
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
       let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
       let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) Atail
       let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        blockMatrixFirstSplitFlat Ablk
       let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        nonsingInv (r + (m + 1) * r) ASplit
       maxEntryNormRect hNTail hNTail AinvTail *
            maxEntryNormRect hNSplit hNSplit ASplit ≤
          maxEntryNormRect hNSplit hNSplit AinvSplit *
            maxEntryNormRect hNTail hNTail Atail) →
      Higham13Eq1322InverseRatioSourceChain hr n m
        (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13Eq1322InverseRatioSourceChain hr n (m + 1) Ablk pivotInv

/-- The inverse-ratio source-chain certificate carries determinant
    nonsingularity for its current block matrix. -/
theorem Higham13Eq1322InverseRatioSourceChain.det_ne_zero {r n : ℕ}
    {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 := by
  intro m Ablk pivotInv hcert
  cases hcert with
  | one hdet _ =>
      simpa using hdet
  | succ _ hdetFlat _ _ _ _ =>
      simpa using hdetFlat

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    a recursive inverse-ratio source certificate instantiates the ambient
    exact-κ budget chain.

    This removes the prebuilt ambient-chain hypothesis from the inverse-ratio
    route.  The inverse-ratio comparison itself remains the visible
    source-side mathematical obligation at each recursive Schur tail. -/
theorem Higham13Eq1322InverseRatioSourceChain.to_blockLUBudgetChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
          (Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert)
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
  | succ hpivot hdetFlat hsn hNn hInvRatio hTail =>
      have ih :=
        Higham13Eq1322InverseRatioSourceChain.to_blockLUBudgetChain
          (r := r) (n := n) hr hTail
      have hTailPos :
          0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos _) hr)
            (blockMatrixFlatFin (blockSchur _ (pivotInv 0))) :=
        maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
          hr _ pivotInv hpivot
      dsimp only at ih ⊢
      simpa using
        higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_flat_matrix_stage_history_exact_kappa_of_det_ne_zero
          hr _ pivotInv hpivot hTailPos hdetFlat n hsn hNn hInvRatio ih

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    full recursive Eq.13.22 product witness from the inverse-ratio source
    certificate. -/
theorem Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
          (Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert)
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
    Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert
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
      Higham13Eq1322InverseRatioSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the inverse-ratio source
    certificate plus the remaining source-side `rho <= 2` theorem. -/
theorem Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
          (Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert)
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
    Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert
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
      Higham13Eq1322InverseRatioSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the inverse-ratio source
    certificate, with the `rho <= 2` side condition supplied by the
    matrix-stage product-bound/diagonal-update BDD route. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
    Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert
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
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) (n := n) hr hcert
      (by
        simpa [hm, hN, A0, G, Ainv, hApos] using
          higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
            hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
            hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the inverse-ratio source-chain point-row product
    witness.

    This is the source-shaped companion to
    `Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update`:
    callers may provide the active source-table reciprocal equality instead of
    the raw pivot product bound. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` BDD form of the inverse-ratio source-chain product/update
    witness.

    The source column BDD hypothesis is stated with matrix `∞` block norms.
    This wrapper derives the max-entry BDD premise consumed by the existing
    product/update route and derives the diagonal max-entry lower certificate
    from the nonpositive source bounds.  The inverse-ratio comparisons,
    structured product estimate, and diagonal-update table remain explicit. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/matrix-`∞` BDD form of the inverse-ratio source-chain
    product/update witness. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
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
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hReciprocal hProduct hDiagUpdate

end NumStability
