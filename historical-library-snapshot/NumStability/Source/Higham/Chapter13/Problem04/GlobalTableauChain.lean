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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation21
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.LocalNormBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.GlobalTableauChain

This module formalizes the source-facing Chapter 13 statements for
`Problem04.GlobalTableauChain`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    recursive source certificate for the fixed ambient global-growth-tableau
    route.

    This is the source-faithful route recorded in the Chapter 13 proof ledger:
    every recursive Schur tail is measured against one ambient tableau
    `(Aglob,Gglob)` and one ambient inverse certificate `AinvGlob`, rather than
    against a locally normalized tail growth factor.  The constructor exposes
    exactly the remaining source obligations: each tail Schur complement must be
    contained in the ambient tableau, the current tail inverse entries must be
    bounded by the ambient inverse certificate, and the first row/terminal block
    must satisfy the ambient upper budget. -/
inductive Higham13Eq1322GlobalTableauSourceChain {r N : ℕ}
    (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob) (n : ℕ) :
    (m : ℕ) →
      (Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) →
      (ℕ → Matrix (Fin r) (Fin r) ℝ) → Prop
  | one {Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hUpper :
        blockMaxNorm (Nat.succ_pos 0) hr Ablk ≤
          growthFactorEntry hN Aglob Gglob hApos *
            maxEntryNormRect hN hN Aglob) :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n 0 Ablk pivotInv
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
      (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
      (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob)
      (hSchur_le_G :
        maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
            (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFirstSplitA22 Ablk -
              blockMatrixFirstSplitA21 Ablk *
                ⅟(blockMatrixFirstSplitA11 Ablk) *
                  blockMatrixFirstSplitA12 Ablk) ≤
          maxEntryNorm hN Gglob)
      (hAinv_entry :
        ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
          |(⅟(Matrix.fromBlocks
              (blockMatrixFirstSplitA11 Ablk)
              (blockMatrixFirstSplitA12 Ablk)
              (blockMatrixFirstSplitA21 Ablk)
              (blockMatrixFirstSplitA22 Ablk)) :
            Matrix (Fin r ⊕ Fin ((m + 1) * r))
              (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
            maxEntryNormRect hN hN AinvGlob)
      (hFirstRow :
        ∀ j : Fin ((m + 1) + 1),
          maxEntryNorm hr (Ablk 0 j) ≤
            growthFactorEntry hN Aglob Gglob hApos *
              maxEntryNormRect hN hN Aglob)
      (hTail :
        Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
          hApos n m (blockSchur Ablk (pivotInv 0))
          (fun q => pivotInv (q + 1))) :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n (m + 1) Ablk pivotInv

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22): the
fixed-ambient global tableau gives the printed condition comparison for the
*actual* Algorithm 13.3 Schur tail,

`κ_max(S) ≤ ρ(A,G) κ_max(A)`.

Here `S` is the flattened recursive tail `blockSchur Ablk (pivotInv 0)`,
`ρ(A,G)` is the one ambient matrix-stage growth factor, and the inverse in
`κ_max(S)` is the repository's constructive `nonsingInv`.  The proof eliminates
the successor certificate, identifies its pivot with the exact first-block
inverse, obtains `‖S‖_max ≤ ρ ‖A‖_max` from tableau containment, and obtains
`‖S⁻¹‖_max ≤ ‖A⁻¹‖_max` from the lower-right block of the actual parent inverse.
No condition-number conclusion is assumed. -/
theorem Higham13Eq1322GlobalTableauSourceChain.head_schur_condition_exact_kappa
    {r N n m : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    {Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ}
    {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
    (hcert : Higham13Eq1322GlobalTableauSourceChain
      hr hN Aglob Gglob AinvGlob hApos n (m + 1) Ablk pivotInv) :
    let hs : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
    let S : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
      blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
    maxEntryNormRect hs hs S *
        maxEntryNormRect hs hs (nonsingInv ((m + 1) * r) S) ≤
      growthFactorEntry hN Aglob Gglob hApos *
        (maxEntryNormRect hN hN Aglob *
          maxEntryNormRect hN hN AinvGlob) := by
  cases hcert with
  | @succ m Ablk pivotInv instA11 instSchur instFull hpivot hsn hA_le_G
      hSchur_le_G hAinv_entry hFirstRow hTail =>
      dsimp only
      let hs : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
      let A11inv : Matrix (Fin r) (Fin r) ℝ :=
        @Invertible.invOf (Matrix (Fin r) (Fin r) ℝ) _ _
          (blockMatrixFirstSplitA11 Ablk) instA11
      let S : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
        blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
      let Sdisplay : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
        blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk * A11inv *
            blockMatrixFirstSplitA12 Ablk
      have hpivot' : pivotInv 0 = A11inv := by
        simpa [A11inv] using hpivot
      have hSeq : S = Sdisplay := by
        simpa [S, Sdisplay, hpivot'] using
          (blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
            Ablk A11inv).symm
      have hRho : 0 ≤ growthFactorEntry hN Aglob Gglob hApos := by
        unfold growthFactorEntry
        exact div_nonneg (maxEntryNorm_nonneg hN Gglob) (le_of_lt hApos)
      have hSbound :
          maxEntryNormRect hs hs S ≤
            growthFactorEntry hN Aglob Gglob hApos *
              maxEntryNormRect hN hN Aglob := by
        exact maxEntryNormRect_le_growthFactorEntry_mul_of_le_maxEntryNorm
          hN hs Aglob Gglob S hApos
            (by simpa [hSeq, Sdisplay, A11inv] using hSchur_le_G)
      have hInvS : Invertible Sdisplay := by
        simpa [Sdisplay, A11inv] using instSchur
      let Sinv : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
        @Invertible.invOf
          (Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) _ _
          Sdisplay hInvS
      have hSinvRight : IsRightInverse ((m + 1) * r) Sdisplay Sinv := by
        have hmul : Sdisplay * Sinv = 1 := by
          simpa [Sinv] using hInvS.mul_invOf_self
        intro i j
        have hentry := congrArg
          (fun M : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ => M i j)
          hmul
        simpa [Matrix.mul_apply] using hentry
      have hSinvEq :
          nonsingInv ((m + 1) * r) S = Sinv := by
        rw [hSeq]
        exact nonsingInv_eq_of_isRightInverse Sdisplay Sinv hSinvRight
      have hSinvbound :
          maxEntryNormRect hs hs (nonsingInv ((m + 1) * r) S) ≤
            maxEntryNormRect hN hN AinvGlob := by
        rw [hSinvEq]
        letI : Invertible Sdisplay := hInvS
        letI := instFull
        simpa [Sinv, Sdisplay, A11inv] using
          (higham13_problem13_4_Sinv_maxEntryNormRect_from_block_inverse
            hs
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)
            hAinv_entry)
      exact
        higham13_problem13_4_schur_kappa_maxEntryNormRect_from_certificates
          hs S (nonsingInv ((m + 1) * r) S) hRho hSbound hSinvbound le_rfl

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    base case for the fixed-ambient global-tableau source chain.

    The source chain's terminal one-block obligation is exactly the ambient
    upper-budget condition.  If the terminal block is contained in the global
    growth tableau `Gglob`, the formal growth-factor definition supplies that
    upper budget with no additional local normalization. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.one_of_blockMaxNorm_le_global_tableau
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    {Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ}
    {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
    (hUpperG : blockMaxNorm (Nat.succ_pos 0) hr Ablk ≤
      maxEntryNorm hN Gglob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
      hApos n 0 Ablk pivotInv := by
  refine Higham13Eq1322GlobalTableauSourceChain.one ?_
  exact
    blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
      hN (Nat.succ_pos 0) hr Aglob Gglob Ablk hApos hUpperG

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    terminal recorded Schur tail for the global matrix-stage tableau.

    Any one-block Schur tail recorded by the matrix-product Algorithm 13.3
    stage history is contained in the same ambient growth tableau.  Hence it is
    a valid terminal certificate for the fixed-ambient Eq.13.22 source chain. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.one_from_matrix_stage_history_tail_exact_kappa
    {M r N n : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv tailPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (k : ℕ) (hk : k ≤ M) (tail : Fin 1 → Fin M) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos n 0
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tail)
      tailPivotInv := by
  refine
    Higham13Eq1322GlobalTableauSourceChain.one_of_blockMaxNorm_le_global_tableau
      hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos ?_
  rw [← maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm
    (Nat.succ_pos 0) hr
    (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tail)]
  exact
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
      hN hM hr (Nat.succ_pos 0) A pivotInv k hk tail

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    successor constructor for recorded active tails in the global tableau.

    This is the all-tail analogue of the first-split global-tableau
    constructor.  The recorded stage-`k` tail supplies the first-row upper
    budget from global tableau containment, its local Schur complement is
    identified with the recorded stage-`k+1` successor tail, and the successor
    Schur containment follows from the same matrix-stage history.  The ambient
    inverse-entry certificate remains explicit because that source comparison
    is one of the remaining Problem 13.4 mathematical obligations. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_exact_kappa
    {M r N m n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob)
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos n (m + 1)
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
      (fun q => pivotInv (k + q)) := by
  classical
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  let A11_inv : Matrix (Fin r) (Fin r) ℝ :=
    ⅟(blockMatrixFirstSplitA11 Ablk)
  have htail_eq :
      higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc =
        blockSchur Ablk A11_inv := by
    have h :=
      higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
        A pivotInv hkM tailFull tailSucc h0 hsucc hactive
    simpa [Ablk, A11_inv, hpivot] using h.symm
  have hAblk_le_G :
      blockMaxNorm hmFull hr Ablk ≤ maxEntryNorm hN G := by
    rw [← maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hmFull hr Ablk]
    simpa [G, Ablk] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        hN hM hr hmFull A pivotInv k (Nat.le_of_lt hkM) tailFull
  have hSchur_le_G :
      maxEntryNormRect (Nat.mul_pos hmTail hr)
          (Nat.mul_pos hmTail hr)
          (blockMatrixFirstSplitA22 Ablk -
            blockMatrixFirstSplitA21 Ablk *
              ⅟(blockMatrixFirstSplitA11 Ablk) *
                blockMatrixFirstSplitA12 Ablk) ≤
        maxEntryNorm hN G := by
    have hS :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        hN hM hr hmTail A pivotInv (k + 1) (Nat.succ_le_of_lt hkM) tailSucc
    rw [htail_eq] at hS
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
      Ablk A11_inv]
    simpa [G, Ablk, A11_inv, maxEntryNormRect_eq_maxEntryNorm
      (Nat.mul_pos hmTail hr)] using hS
  have hFirstRow :
      ∀ j : Fin ((m + 1) + 1),
        maxEntryNorm hr (Ablk 0 j) ≤
          growthFactorEntry hN Aglob G hApos *
            maxEntryNormRect hN hN Aglob := by
    have hInput :
        blockMaxNorm hmFull hr Ablk ≤
          growthFactorEntry hN Aglob G hApos *
            maxEntryNormRect hN hN Aglob :=
      blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
        hN hmFull hr Aglob G Ablk hApos hAblk_le_G
    intro j
    exact le_trans (block_le_blockMaxNorm hmFull hr Ablk 0 j) hInput
  have hpivot0 :
      (fun q : ℕ => pivotInv (k + q)) 0 =
        ⅟(blockMatrixFirstSplitA11 Ablk) := by
    simpa [Ablk] using hpivot
  have hTail' :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n m
        (blockSchur Ablk ((fun q : ℕ => pivotInv (k + q)) 0))
        (fun q => pivotInv (k + (q + 1))) := by
    rw [htail_eq] at hTail
    simpa [G, Ablk, A11_inv, hpivot] using hTail
  simpa [G, Ablk] using
    (Higham13Eq1322GlobalTableauSourceChain.succ
      (hr := hr) (hN := hN) (Aglob := Aglob) (Gglob := G)
      (AinvGlob := AinvGlob) (hApos := hApos) (n := n)
      (Ablk := Ablk) (pivotInv := fun q : ℕ => pivotInv (k + q))
      hpivot0 hsn hA_le_G hSchur_le_G hAinv_entry hFirstRow hTail')

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    successor constructor with automatic Schur-tail inverse-entry handoff.

    This is the reusable all-tail dependency behind the finite two- and
    three-block active-tail constructors.  A caller supplies a way to build the recursive
    tail source chain once the tail inverse-entry certificate is known; this
    theorem derives that tail certificate from the parent block-inverse
    certificate using the first-split Schur-tail handoff, then invokes the
    recorded active-tail successor constructor. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa
    {M r N m n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob)
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos n (m + 1)
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
      (fun q => pivotInv (k + q)) := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  let Aparent : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull
  let Atail : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc
  let A11_inv : Matrix (Fin r) (Fin r) ℝ :=
    ⅟(blockMatrixFirstSplitA11 Aparent)
  have htail_eq : Atail = blockSchur Aparent A11_inv := by
    have h :=
      higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
        A pivotInv hkM tailFull tailSucc h0 hsucc hactive
    simpa [Aparent, Atail, A11_inv, hpivot] using h.symm
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Atail)
      (blockMatrixFirstSplitA12 Atail)
      (blockMatrixFirstSplitA21 Atail)
      (blockMatrixFirstSplitA22 Atail)) :=
    higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
      (Ablk := Aparent) (A11_inv := A11_inv) (Atail := Atail) htail_eq
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA12 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA21 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA22 (blockSchur Aparent A11_inv))) :=
    higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
      (Ablk := Aparent) (A11_inv := A11_inv)
      (Atail := blockSchur Aparent A11_inv) rfl
  have hAinv_tail_block :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA12 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA21 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA22 (blockSchur Aparent A11_inv)))) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    simpa [Aparent, A11_inv] using
      (higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse
        (Ablk := Aparent) (A11_inv := A11_inv)
        (hA11_inv := by rfl)
        (normAinv := maxEntryNormRect hN hN AinvGlob)
        (by simpa [Aparent] using hAinv_entry))
  have hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Atail)
            (blockMatrixFirstSplitA12 Atail)
            (blockMatrixFirstSplitA21 Atail)
            (blockMatrixFirstSplitA22 Atail)) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    simpa [htail_eq] using hAinv_tail_block
  have hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n m
        Atail (fun q => pivotInv (k + (q + 1))) := by
    simpa [G, Atail] using hTailFromEntry hAinv_tail
  simpa [G, Aparent] using
    (Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_exact_kappa
      (M := M) (r := r) (N := N) (m := m) (n := n) (k := k)
      hr hN hM Aglob AinvGlob A pivotInv hApos hkM
      tailFull tailSucc h0 hsucc hactive hpivot hsn hA_le_G
      hAinv_entry
      (by simpa [Atail] using hTail))

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    a single ambient dimension bound supplies every active-suffix tail budget.

    If the ambient block matrix has `M` block rows and `M*r <= n`, then any
    recorded active suffix of block length `m+1` inside that ambient matrix has
    scalar dimension `(m+1)*r <= n`. -/
theorem higham13_activeSuffix_dimension_budget_of_global_bound
    {M r n : ℕ}
    (hMnr : (((M * r : ℕ) : ℝ) ≤ (n : ℝ))) :
    ∀ {m k : ℕ}, k + (m + 1) ≤ M →
      (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ) := by
  intro m k hkm
  have hmM : m + 1 ≤ M := by omega
  have hmul : (m + 1) * r ≤ M * r :=
    Nat.mul_le_mul_right r hmM
  exact le_trans (by exact_mod_cast hmul) hMnr

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    canonical all-active-suffix global-tableau source chain.

    This theorem closes the recursive `hTail` packaging obligation for the
    canonical active suffixes of Algorithm 13.3.  It does not assume the source
    chain itself: callers still supply the genuine per-stage source obligations
    exposed by the book route, namely current-tail invertibility, first-pivot
    equality, the dimension budget, ambient growth-tableau containment, and the
    current inverse-entry comparison.  The Schur-tail inverse-entry comparison
    is then propagated recursively by
    `succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa`. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
    {M r N n : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hsnAll : ∀ {m k : ℕ} (_ : k + (m + 1) ≤ M),
      (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (m + 1) hkm)))
    (hInvSchur : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
              (m + 1) hkm) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                (m + 1) hkm) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (m + 1) hkm)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (m + 1) hkm)))
    (hpivotAll : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (m + 1) hkm))) :
    ∀ (m k : ℕ) (hkm : k + (m + 1) ≤ M),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm)))] →
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm)
        (fun q => pivotInv (k + q)) := by
  classical
  intro m
  induction m with
  | zero =>
      intro k hkm _ _
      exact
        Higham13Eq1322GlobalTableauSourceChain.one_from_matrix_stage_history_tail_exact_kappa
          hr hN hM Aglob AinvGlob A pivotInv (fun q => pivotInv (k + q))
          hApos k (by omega)
          (higham13_algorithm13_3_activeSuffixTail M k 1 hkm)
  | succ m ih =>
      intro k hkm _ hAinv_entry
      have hkM : k < M := by omega
      have htail : k + 1 + (m + 1) ≤ M := by omega
      let tailFull : Fin ((m + 1) + 1) → Fin M :=
        higham13_algorithm13_3_activeSuffixTail M k ((m + 1) + 1) hkm
      let tailSucc : Fin (m + 1) → Fin M :=
        higham13_algorithm13_3_activeSuffixTail M (k + 1) (m + 1) htail
      letI : Invertible
          (blockMatrixFirstSplitA11
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) := by
        simpa [tailFull, higham13_algorithm13_3_activeSuffixStageTailBlock] using
          (hInvA11 (m := m) (k := k) hkm)
      letI : Invertible
          (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
            blockMatrixFirstSplitA21
                (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
              ⅟(blockMatrixFirstSplitA11
                  (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
                blockMatrixFirstSplitA12
                  (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) := by
        simpa [tailFull, higham13_algorithm13_3_activeSuffixStageTailBlock] using
          (hInvSchur (m := m) (k := k) hkm)
      have h0 : tailFull 0 = ⟨k, hkM⟩ := by
        simpa [tailFull] using
          higham13_algorithm13_3_activeSuffixTail_zero (M := M) (k := k)
            (b := m + 1) hkm hkM
      have hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i := by
        intro i
        simpa [tailFull, tailSucc] using
          higham13_algorithm13_3_activeSuffixTail_succ (M := M) (k := k)
            (b := m) hkm htail i
      have hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val := by
        intro i
        exact
          higham13_algorithm13_3_activeSuffixTail_active (M := M) (k := k)
            (b := m) htail i
      have hpivot :
          pivotInv k =
            ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) := by
        simpa [tailFull, higham13_algorithm13_3_activeSuffixStageTailBlock] using
          (hpivotAll (m := m) (k := k) hkm)
      refine
        Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa
          (M := M) (r := r) (N := N) (m := m) (n := n) (k := k)
          hr hN hM Aglob AinvGlob A pivotInv hApos hkM
          tailFull tailSucc h0 hsucc hactive hpivot (hsnAll htail) hA_le_G
          ?_ ?_
      · simpa [tailFull, higham13_algorithm13_3_activeSuffixStageTailBlock] using
          hAinv_entry
      · intro _ hAinv_tail
        have hTail := ih (k + 1) htail hAinv_tail
        simpa [tailSucc, higham13_algorithm13_3_activeSuffixStageTailBlock,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    canonical all-active-suffix source chain from one ambient dimension bound.

    This is the global-dimension-bound companion to
    `Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`;
    it derives the per-tail `(m+1)*r <= n` table internally from `M*r <= n`. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound
    {M r N n : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hMnr : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hInvA11 : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (m + 1) hkm)))
    (hInvSchur : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      Invertible
        (blockMatrixFirstSplitA22
            (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
              (m + 1) hkm) -
          blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                (m + 1) hkm) *
            ⅟(blockMatrixFirstSplitA11
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (m + 1) hkm)) *
              blockMatrixFirstSplitA12
                (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
                  (m + 1) hkm)))
    (hpivotAll : ∀ {m k : ℕ} (hkm : k + ((m + 1) + 1) ≤ M),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (m + 1) hkm))) :
    ∀ (m k : ℕ) (hkm : k + (m + 1) ≤ M),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm)))] →
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k m hkm)
        (fun q => pivotInv (k + q)) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      hr hN hM Aglob AinvGlob A pivotInv hApos hA_le_G
      (fun hkm =>
        higham13_activeSuffix_dimension_budget_of_global_bound hMnr hkm)
      hInvA11 hInvSchur hpivotAll

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    canonical all-active-suffix source chain from determinant tables.

    This is a determinant-table companion to
    `activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound`.
    It derives the active full-tail, pivot-block, and Schur-complement
    invertibility instances internally from determinant-nonzero tables, so the
    caller states source nonsingularity data as determinants rather than Lean
    typeclass plumbing.  The source inverse-entry comparison table remains a
    genuine mathematical premise. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables
    {M r N n : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hMnr : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    ∀ (q k : ℕ) (hkq : k + (q + 1) ≤ M),
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n q
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq)
        (fun s => pivotInv (k + s)) := by
  classical
  let hInvFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ M),
      Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) := by
    intro q k hkq
    let T : Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ :=
      Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
    letI : Invertible (Matrix.det T) := invertibleOfNonzero (by
      simpa [T] using hDetFull (q := q) (k := k) hkq)
    simpa [T] using Matrix.invertibleOfDetInvertible T
  let hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    let A11 : Matrix (Fin r) (Fin r) ℝ :=
      blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
          (q + 1) hkq)
    letI : Invertible (Matrix.det A11) := invertibleOfNonzero (by
      simpa [A11] using hDetA11 (q := q) (k := k) hkq)
    simpa [A11] using Matrix.invertibleOfDetInvertible A11
  let hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M),
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
    let Tail :=
      higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
        (q + 1) hkq
    let A11 := blockMatrixFirstSplitA11 Tail
    let A12 := blockMatrixFirstSplitA12 Tail
    let A21 := blockMatrixFirstSplitA21 Tail
    let A22 := blockMatrixFirstSplitA22 Tail
    letI : Invertible A11 := by
      simpa [Tail, A11] using hInvA11 (q := q) (k := k) hkq
    letI : Invertible (Matrix.fromBlocks A11 A12 A21 A22) := by
      simpa [Tail, A11, A12, A21, A22] using
        hInvFull (q := q + 1) (k := k) hkq
    simpa [Tail, A11, A12, A21, A22] using
      Matrix.invertibleOfFromBlocks₁₁Invertible A11 A12 A21 A22
  let hpivotAll' : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ M),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) := by
    intro q k hkq
    letI : Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) :=
      hInvA11 (q := q) (k := k) hkq
    exact hpivotAll hkq
  intro q k hkq
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) :=
    hInvFull (q := q) (k := k) hkq
  exact
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound
      hr hN hM Aglob AinvGlob A pivotInv hApos hA_le_G hMnr
      hInvA11 hInvSchur hpivotAll' q k hkq (hAinvEntryAll hkq)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first Schur-tail specialization of the canonical active-suffix source
    chain.

    This is the direct first-split consumer of
    `activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`.
    It identifies the canonical stage-one suffix with the first Schur
    complement `blockSchur A (pivotInv 0)`, so a first-split proof can replace
    a supplied recursive `hTail` by explicit active-suffix source obligations
    and the current first-Schur-tail inverse-entry comparison. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
    {m r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr A pivotInv))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
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
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0))))]
    (hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0)))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr A pivotInv)
      AinvGlob hApos n m
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  classical
  have htail : 1 + (m + 1) ≤ (m + 1) + 1 := by omega
  have hStage :
      higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail =
        blockSchur A (pivotInv 0) := by
    exact higham13_algorithm13_3_activeSuffixStageTailBlock_one_eq_blockSchur
      A pivotInv (pivotInv 0) htail rfl
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))) := by
    simpa [hStage] using
      (inferInstance : Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
        (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
        (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
        (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0)))))
  have hAinv_active :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    intro i j
    simpa [hStage] using hAinv_tail i j
  have hcert :=
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      (M := (m + 1) + 1) (r := r) (N := N) (n := n)
      hr hN (Nat.succ_pos (m + 1)) Aglob AinvGlob A pivotInv hApos hA_le_G
      hsnAll hInvA11 hInvSchur hpivotAll m 1 htail hAinv_active
  simpa [hStage, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first Schur-tail source chain with parent inverse-entry handoff.

    This is the source-facing first-split inverse-entry propagation step.  A
    parent first-split inverse-entry comparison implies the first Schur-tail
    comparison by the block inverse formula, and the existing active-suffix
    recursion then propagates the comparison through all later tails.  Thus the
    first Schur-tail inverse-entry table is derived rather than supplied as a
    separate premise. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa
    {m r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr A pivotInv))
    [Invertible (blockMatrixFirstSplitA11 A)]
    [Invertible (blockMatrixFirstSplitA22 A -
      blockMatrixFirstSplitA21 A * ⅟(blockMatrixFirstSplitA11 A) *
        blockMatrixFirstSplitA12 A)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 A))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
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
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 A)
            (blockMatrixFirstSplitA12 A)
            (blockMatrixFirstSplitA21 A)
            (blockMatrixFirstSplitA22 A)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr A pivotInv)
      AinvGlob hApos n m
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  classical
  letI : Invertible
      (blockMatrixFirstSplitA22 A -
        blockMatrixFirstSplitA21 A * pivotInv 0 *
          blockMatrixFirstSplitA12 A) := by
    simpa [hpivot] using
      (inferInstance : Invertible (blockMatrixFirstSplitA22 A -
        blockMatrixFirstSplitA21 A * ⅟(blockMatrixFirstSplitA11 A) *
          blockMatrixFirstSplitA12 A))
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0)))) :=
    higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
      (Ablk := A) (A11_inv := pivotInv 0)
      (Atail := blockSchur A (pivotInv 0)) rfl
  have hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0)))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    simpa [hpivot] using
      (higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse
        (Ablk := A) (A11_inv := pivotInv 0)
        (hA11_inv := hpivot)
        (normAinv := maxEntryNormRect hN hN AinvGlob)
        (by simpa using hAinv_parent))
  exact
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      hr hN Aglob AinvGlob A pivotInv hApos hA_le_G
      hsnAll hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first Schur-tail source chain with canonical parent inverse-entry handoff.

    This specialization of
    `firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa`
    derives the parent first-split inverse-entry comparison from the canonical
    ambient `nonsingInv` of `blockMatrixFirstSplitFlat A`.  The remaining
    obligations are the active-suffix pivot and Schur-complement source data. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_canonical_parent_inverse_entry_exact_kappa
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat A))
    (hA_le_G :
      maxEntryNorm hN (blockMatrixFirstSplitFlat A) ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr A pivotInv))
    [Invertible (blockMatrixFirstSplitA11 A)]
    [Invertible (blockMatrixFirstSplitA22 A -
      blockMatrixFirstSplitA21 A * ⅟(blockMatrixFirstSplitA11 A) *
        blockMatrixFirstSplitA12 A)]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A))]
    (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 A))
    (hsnAll : ∀ {q k : ℕ} (_ : k + (q + 1) ≤ (m + 1) + 1),
      (((q + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
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
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq))) :
    Higham13Eq1322GlobalTableauSourceChain hr hN (blockMatrixFirstSplitFlat A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr A pivotInv)
      (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
      hApos n m
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  classical
  have hAinv_parent :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 A)
            (blockMatrixFirstSplitA12 A)
            (blockMatrixFirstSplitA21 A)
            (blockMatrixFirstSplitA22 A)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN
            (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A)) := by
    exact higham13_problem13_4_firstSplit_parent_inverse_entry_bound_from_nonsingInv
      hN A
  exact
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_parent_inverse_entry_exact_kappa
      hr hN (blockMatrixFirstSplitFlat A)
      (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat A))
      A pivotInv hApos hA_le_G hpivot hsnAll hInvA11 hInvSchur hpivotAll
      hAinv_parent

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first Schur-tail source chain from one first-split dimension bound.

    This wrapper derives the active-suffix per-tail dimension table from the
    global first-split bound `((m+1)+1)*r <= n`.  The remaining hypotheses are
    the genuine source obligations: active pivot/Schur invertibility, pivot
    identities, and the first Schur-tail inverse-entry comparison. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound
    {m r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr A pivotInv))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hInvA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hInvSchur : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
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
                  (q + 1) hkq)))
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
      (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0))))]
    (hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA12 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA21 (blockSchur A (pivotInv 0)))
            (blockMatrixFirstSplitA22 (blockSchur A (pivotInv 0)))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr A pivotInv)
      AinvGlob hApos n m
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      hr hN Aglob AinvGlob A pivotInv hApos hA_le_G
      (fun hkq =>
        higham13_activeSuffix_dimension_budget_of_global_bound
          (M := (m + 1) + 1) (r := r) (n := n) hFulln hkq)
      hInvA11 hInvSchur hpivotAll hAinv_tail

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first Schur-tail source chain from determinant tables.

    This specializes the determinant-table active-suffix wrapper to the
    canonical first Schur complement `blockSchur A (pivotInv 0)`.  The theorem
    removes the separate active pivot/Schur invertibility and first-Schur-tail
    invertibility premises, deriving them from determinant-nonzero tables.
    It still requires the genuine all-active-suffix inverse-entry comparison
    table needed by the Problem 13.4 source route. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.firstSchurTail_activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables
    {m r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
            hN (Nat.succ_pos (m + 1)) hr A pivotInv))
    (hFulln : (((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hDetFull : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) ≠ 0)
    (hDetA11 : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      Matrix.det
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)) ≠ 0)
    (hpivotAll : ∀ {q k : ℕ} (hkq : k + ((q + 1) + 1) ≤ (m + 1) + 1),
      [Invertible
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq))] →
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k
            (q + 1) hkq)))
    (hAinvEntryAll : ∀ {q k : ℕ} (hkq : k + (q + 1) ≤ (m + 1) + 1),
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq)))] →
      ∀ i j : Fin r ⊕ Fin (q * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv k q hkq))) :
          Matrix (Fin r ⊕ Fin (q * r)) (Fin r ⊕ Fin (q * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr A pivotInv)
      AinvGlob hApos n m
      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) := by
  classical
  have htail : 1 + (m + 1) ≤ (m + 1) + 1 := by omega
  have hStage :
      higham13_algorithm13_3_activeSuffixStageTailBlock A pivotInv 1 m htail =
        blockSchur A (pivotInv 0) := by
    exact higham13_algorithm13_3_activeSuffixStageTailBlock_one_eq_blockSchur
      A pivotInv (pivotInv 0) htail rfl
  have hcert :=
    Higham13Eq1322GlobalTableauSourceChain.activeSuffix_from_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_global_dimension_bound_of_det_tables
      (M := (m + 1) + 1) (r := r) (N := N) (n := n)
      hr hN (Nat.succ_pos (m + 1)) Aglob AinvGlob A pivotInv
      hApos hA_le_G hFulln hDetFull hDetA11 hpivotAll hAinvEntryAll
      m 1 htail
  simpa [hStage, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    two-block active recorded tail for the global tableau.

    This composes the all-tail successor constructor with the terminal
    one-block matrix-stage constructor.  It is the first closed recursive
    instance of the fixed-ambient global-tableau chain from recorded active
    tails: the terminal Schur tail no longer has to be supplied separately.
    The ambient inverse-entry/source comparison remains explicit. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos n 1
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
      (fun q => pivotInv (k + q)) := by
  classical
  refine
    Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_exact_kappa
      (M := M) (r := r) (N := N) (m := 0) (n := n) (k := k)
      hr hN hM Aglob AinvGlob A pivotInv hApos hkM
      tailFull tailSucc h0 hsucc hactive hpivot ?_ hA_le_G hAinv_entry ?_
  · simpa using hsn
  · exact
      Higham13Eq1322GlobalTableauSourceChain.one_from_matrix_stage_history_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) hr hN hM
        Aglob AinvGlob A pivotInv
        (fun q => pivotInv (k + (q + 1))) hApos (k + 1)
        (Nat.succ_le_of_lt hkM) tailSucc

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    three-block active recorded tail for the fixed ambient global tableau.

    This composes the active-tail successor constructor with the closed
    two-block active-tail constructor.  The new ingredient is the recursive
    Schur-tail inverse-entry handoff: a single inverse-entry certificate for
    the parent three-block tail supplies the two-block Schur-tail inverse-entry
    certificate automatically, so callers no longer state that first recursive
    tail certificate separately. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.three_from_matrix_stage_history_active_tail_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
      AinvGlob hApos n 2
      (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
      (fun q => pivotInv (k + q)) := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  let Aparent : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull
  let Atail : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid
  let A11_inv : Matrix (Fin r) (Fin r) ℝ :=
    ⅟(blockMatrixFirstSplitA11 Aparent)
  have htail_eq : Atail = blockSchur Aparent A11_inv := by
    have h :=
      higham13_algorithm13_3_schurStageMatrixTailBlock_succ_active_eq_blockSchur
        A pivotInv hkM tailFull tailMid h0 hsucc hactive
    simpa [Aparent, Atail, A11_inv, hpivot] using h.symm
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 Atail)
      (blockMatrixFirstSplitA12 Atail)
      (blockMatrixFirstSplitA21 Atail)
      (blockMatrixFirstSplitA22 Atail)) :=
    higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
      (Ablk := Aparent) (A11_inv := A11_inv) (Atail := Atail) htail_eq
  letI : Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA12 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA21 (blockSchur Aparent A11_inv))
      (blockMatrixFirstSplitA22 (blockSchur Aparent A11_inv))) :=
    higham13_problem13_4_schurTail_fromBlocks_invertible_of_schur_invertible
      (Ablk := Aparent) (A11_inv := A11_inv)
      (Atail := blockSchur Aparent A11_inv) rfl
  have hAinv_tail_block :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA12 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA21 (blockSchur Aparent A11_inv))
            (blockMatrixFirstSplitA22 (blockSchur Aparent A11_inv)))) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    simpa [Aparent, A11_inv] using
      (higham13_problem13_4_firstSplit_schurTail_inverse_entry_bound_from_block_inverse
        (Ablk := Aparent) (A11_inv := A11_inv)
        (hA11_inv := by rfl)
        (normAinv := maxEntryNormRect hN hN AinvGlob)
        (by simpa [Aparent] using hAinv_entry))
  have hAinv_tail :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Atail)
            (blockMatrixFirstSplitA12 Atail)
            (blockMatrixFirstSplitA21 Atail)
            (blockMatrixFirstSplitA22 Atail)) :
          Matrix (Fin r ⊕ Fin (1 * r)) (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob := by
    simpa [htail_eq] using hAinv_tail_block
  have hTailCert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 1
        Atail (fun q => pivotInv ((k + 1) + q)) := by
    simpa [G, Atail] using
      (Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) (k := k + 1)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkSuccM
        tailMid tailLast h1 hsuccTail hactiveTail hpivotTail hsnTail
        hA_le_G hAinv_tail)
  have hTailCert' :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 1
        Atail (fun q => pivotInv (k + (q + 1))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTailCert
  simpa [G, Aparent] using
    (Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_exact_kappa
      (M := M) (r := r) (N := N) (m := 1) (n := n) (k := k)
      hr hN hM Aglob AinvGlob A pivotInv hApos hkM
      tailFull tailMid h0 hsucc hactive hpivot hsnParent hA_le_G
      hAinv_entry
      (by simpa [Atail] using hTailCert'))

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equations (13.22)--(13.23):
    first-split constructor for the fixed-ambient global-tableau source chain
    using the source-faithful matrix-product Algorithm 13.3 stage history.

    This discharges the bookkeeping obligations that the matrix-stage history
    already proves: the ambient initial matrix is contained in the tableau, the
    first Schur complement is a recorded tail of that tableau, the first block
    row is bounded by the ambient upper budget, and the displayed block inverse
    entries are bounded by the canonical `nonsingInv` of the first-split source
    matrix.  The recursive Schur-tail source certificate remains the explicit
    mathematical obligation. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_first_split_exact_kappa
    {m r n : ℕ} (hr : 0 < r) (hN : 0 < r + (m + 1) * r)
    (Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
      Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
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
    (hApos : 0 < maxEntryNorm hN (blockMatrixFirstSplitFlat Ablk))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hTail :
      Higham13Eq1322GlobalTableauSourceChain hr hN
        (blockMatrixFirstSplitFlat Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
        (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
        hApos n m (blockSchur Ablk (pivotInv 0))
        (fun q => pivotInv (q + 1))) :
    Higham13Eq1322GlobalTableauSourceChain hr hN
      (blockMatrixFirstSplitFlat Ablk)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        hN (Nat.succ_pos (m + 1)) hr Ablk pivotInv)
      (nonsingInv (r + (m + 1) * r) (blockMatrixFirstSplitFlat Ablk))
      hApos n (m + 1) Ablk pivotInv := by
  classical
  let hmTail : 0 < m + 1 := Nat.succ_pos m
  let hmFull : 0 < (m + 1) + 1 := Nat.succ_pos (m + 1)
  let A0 : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    blockMatrixFirstSplitFlat Ablk
  let G : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hmFull hr Ablk pivotInv
  let Ainv : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
    nonsingInv (r + (m + 1) * r) A0
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let normA : ℝ := maxEntryNormRect hN hN A0
  have hA_le_G : maxEntryNorm hN A0 ≤ maxEntryNorm hN G := by
    exact le_trans
      (by
        simpa [A0] using
          maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN
            hN hmTail hr Ablk)
      (by
        simpa [G] using
          higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
  have hSchur_le_G :
      maxEntryNormRect (Nat.mul_pos hmTail hr)
          (Nat.mul_pos hmTail hr)
          (blockMatrixFirstSplitA22 Ablk -
            blockMatrixFirstSplitA21 Ablk *
              ⅟(blockMatrixFirstSplitA11 Ablk) *
                blockMatrixFirstSplitA12 Ablk) ≤
        maxEntryNorm hN G := by
    let A11_inv : Matrix (Fin r) (Fin r) ℝ :=
      ⅟(blockMatrixFirstSplitA11 Ablk)
    have htail :
        higham13_algorithm13_3_schurStageMatrixTailBlock
            Ablk pivotInv 1 Fin.succ =
          blockSchur Ablk A11_inv := by
      exact higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
        Ablk pivotInv A11_inv (by simpa [A11_inv] using hpivot)
    have hS :=
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_flat_stage_tail
        hN hmFull hr hmTail Ablk pivotInv 1 (by omega) Fin.succ
    rw [htail] at hS
    rw [blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
      Ablk A11_inv]
    simpa [G, A11_inv, maxEntryNormRect_eq_maxEntryNorm (Nat.mul_pos hmTail hr)]
      using hS
  have hFull_eq :
      Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Ablk)
          (blockMatrixFirstSplitA12 Ablk)
          (blockMatrixFirstSplitA21 Ablk)
          (blockMatrixFirstSplitA22 Ablk) =
        (fun i j : Fin r ⊕ Fin ((m + 1) * r) =>
          A0 (finSumFinEquiv i) (finSumFinEquiv j)) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [A0, blockMatrixFirstSplitA11, blockMatrixFirstSplitFlat]
        | inr j =>
            simp [A0, blockMatrixFirstSplitA12, blockMatrixFirstSplitFlat]
    | inr i =>
        cases j with
        | inl j =>
            simp [A0, blockMatrixFirstSplitA21, blockMatrixFirstSplitFlat]
        | inr j =>
            simp [A0, blockMatrixFirstSplitA22, blockMatrixFirstSplitFlat,
              blockMatrixFlatFin]
  have hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN Ainv := by
    simpa [A0, Ainv] using
      (maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
        hN
        (finSumFinEquiv :
          (Fin r ⊕ Fin ((m + 1) * r)) ≃ Fin (r + (m + 1) * r))
        A0
        (Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Ablk)
          (blockMatrixFirstSplitA12 Ablk)
          (blockMatrixFirstSplitA21 Ablk)
          (blockMatrixFirstSplitA22 Ablk))
        hFull_eq)
  have hFirstRow :
      ∀ j : Fin ((m + 1) + 1),
        maxEntryNorm hr (Ablk 0 j) ≤ rho * normA := by
    have hInput : blockMaxNorm hmFull hr Ablk ≤ rho * normA := by
      simpa [A0, G, rho, normA] using
        blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
          hN hmFull hr A0 G Ablk hApos
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
            hN hmFull hr Ablk pivotInv)
    intro j
    exact le_trans (block_le_blockMaxNorm hmFull hr Ablk 0 j) hInput
  simpa [A0, G, Ainv, rho, normA, hmTail, hmFull] using
    (Higham13Eq1322GlobalTableauSourceChain.succ
      (hr := hr) (hN := hN) (Aglob := A0) (Gglob := G)
      (AinvGlob := Ainv) (hApos := hApos) (n := n)
      (Ablk := Ablk) (pivotInv := pivotInv)
      hpivot hsn hA_le_G hSchur_le_G hAinv_entry hFirstRow hTail)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot right-inverse data carried by the fixed-ambient
    global-tableau source certificate.

    This exposes the pivot identities stored by the recursive global-tableau
    route in the same table form used by the BDD/product-update interfaces.
    The terminal one-block pivot is intentionally not included; all-pivot
    wrappers below isolate that final datum. -/
theorem Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_right_inverse
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩)
            (pivotInv k) := by
  intro m Ablk pivotInv hcert
  induction hcert with
  | one hUpper =>
      intro k hk
      exact (Nat.not_lt_zero k hk).elim
  | @succ m Ablk pivotInv hA11 hSchur hFull hpivot hsn hA_le_G
      hSchur_le_G hAinv_entry hFirstRow hTail ih =>
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
    a fixed-ambient global-tableau source chain. -/
theorem Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_det_ne_zero
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          Matrix.det
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert k hk
  have hRight :=
    Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_right_inverse
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
    full active pivot right-inverse table for a fixed-ambient global-tableau
    source chain, once the final one-block pivot is supplied separately. -/
theorem Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_right_inverse
        hcert k hkm
  · have hle : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have hEq : k = m := Nat.le_antisymm hle hmk
    subst k
    simpa using hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a fixed-ambient global-tableau
    source chain, once the final one-block pivot determinant is supplied
    separately. -/
theorem Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      Higham13Eq1322GlobalTableauSourceChain.nonterminal_pivot_det_ne_zero
        hcert k hkm
  · have hle : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have hEq : k = m := Nat.le_antisymm hle hmk
    subst k
    simpa using hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a fixed-ambient global-tableau
    source chain when the final one-block pivot is supplied as a right-inverse
    certificate. -/
theorem Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final_right_inverse
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      (Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
        hcert hfinal)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot right-inverse table for a fixed-ambient global-tableau source
    chain when the terminal one-block pivot is the canonical `nonsingInv`. -/
theorem Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
  apply Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final hcert
  simpa [hfinalEq] using
    (isInverse_nonsingInv_of_det_ne_zero r
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
        ⟨m, Nat.lt_succ_self m⟩
        ⟨m, Nat.lt_succ_self m⟩) hdet).2

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot determinant table for a fixed-ambient global-tableau source chain
    when the terminal one-block pivot is the canonical `nonsingInv`. -/
theorem Higham13Eq1322GlobalTableauSourceChain.pivot_det_ne_zero_of_final_nonsingInv
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      (Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv
        hcert hdet hfinalEq)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equations (13.22)--(13.23):
    a fixed-ambient global-tableau source chain, plus the terminal pivot
    right-inverse certificate, supplies the active matrix-`∞` column-dominance
    table needed by the mixed Eq.13.23 route. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.matrix_infNorm_active_column_dominance_of_final_right_inverse
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
      SchurStageActiveColumnDom13_7
        (fun k i j => infNorm
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound Ablk
          pivotInv) := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinal
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
      hcert hFinal
  simpa using
    (higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivotRight)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equations (13.22)--(13.23):
    canonical-terminal-pivot form of the global-tableau active matrix-`∞`
    column-dominance source table. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.matrix_infNorm_active_column_dominance_of_final_nonsingInv
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
      SchurStageActiveColumnDom13_7
        (fun k i j => infNorm
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        (higham13_algorithm13_3_diagLowerCertGeneric invDiagBound Ablk
          pivotInv) := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinalDet
    hFinalEq
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv
      hcert hFinalDet hFinalEq
  simpa using
    (higham13_algorithm13_3_matrix_infNorm_active_column_dominance_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound hPivotRight)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equations (13.22)--(13.23):
    a fixed-ambient global-tableau source chain, plus the terminal pivot
    right-inverse certificate, supplies the matrix-`∞` pivot-product table
    needed by the mixed Eq.13.23 route. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_final_right_inverse
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
      ∀ k : ℕ, ∀ hk : k < m + 1,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound Ablk
              pivotInv k ⟨k, hk⟩ ≤
          1 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinal
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDomPi :
      IsBlockDiagDomCol (m + 1)
        (fun i j =>
          ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound :=
    higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
      hcert hFinal
  simpa using
    (higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr invDiagBound Ablk pivotInv hPrefix hDomPi hBound hPivotRight)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 and equations (13.22)--(13.23):
    canonical-terminal-pivot form of the global-tableau matrix-`∞`
    pivot-product source table. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_final_nonsingInv
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
      letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
      ∀ k : ℕ, ∀ hk : k < m + 1,
        infNorm (pivotInv k) *
            higham13_algorithm13_3_diagLowerCertGeneric invDiagBound Ablk
              pivotInv k ⟨k, hk⟩ ≤
          1 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinalDet
    hFinalEq
  letI := Matrix.linftyOpNormedRing (n := Fin r) (α := ℝ)
  have hDomPi :
      IsBlockDiagDomCol (m + 1)
        (fun i j =>
          ‖(fun a b => Ablk i j a b : Fin r → Fin r → ℝ)‖)
        invDiagBound :=
    higham13_blockDiagDomCol_piNorm_of_infNorm hr Ablk invDiagBound hDomInf
  have hPivotRight :
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) :=
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv
      hcert hFinalDet hFinalEq
  simpa using
    (higham13_algorithm13_3_matrix_infNorm_diagLowerCertGeneric_pivot_bound_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos_of_pivot_right_inverse_of_pos_dim
      hr invDiagBound Ablk pivotInv hPrefix hDomPi hBound hPivotRight)

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    a fixed-ambient global-tableau source chain, plus the terminal pivot
    right-inverse certificate, supplies the mixed matrix-`∞`/max-entry
    upper-factor and finite-history growth-factor endpoint.

    The source chain provides all nonterminal pivot certificates; this wrapper
    exposes the same BDD mixed endpoint surface as the other source-chain
    routes while leaving only the terminal pivot datum explicit. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
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
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
      hcert hFinal
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot form of the fixed-ambient global-tableau
    source-chain mixed matrix-`∞`/max-entry endpoint. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
    {r N n : ℕ} {hr : 0 < r} {hN : 0 < N}
    {Aglob Gglob AinvGlob : Fin N → Fin N → ℝ}
    {hApos : 0 < maxEntryNorm hN Aglob} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob
        AinvGlob hApos n m Ablk pivotInv) →
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
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final_nonsingInv
      hcert hFinalDet hFinalEq
  exact
    higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
      (Nat.succ_pos m) hr Ablk pivotInv invDiagBound hPrefix hDomInf hBound
      hPivotRight

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    a fixed-ambient global-tableau source certificate instantiates the
    `Higham13BlockLUBudgetChain` with the ambient exact-`κ` constants.

    This theorem changes the Problem 13.4 recursive route from a local-tail
    comparison problem into the source obligations exposed by
    `Higham13Eq1322GlobalTableauSourceChain`: ambient Schur-tableau containment,
    ambient inverse-entry control, and first-row/terminal upper budgets. -/
theorem Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
        (maxEntryNormRect hN hN Aglob *
          maxEntryNormRect hN hN AinvGlob)) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
          (maxEntryNormRect hN hN Aglob *
            maxEntryNormRect hN hN AinvGlob))
        (growthFactorEntry hN Aglob Gglob hApos *
          maxEntryNormRect hN hN Aglob)
        m Ablk pivotInv := by
  intro m Ablk pivotInv hcert
  induction hcert with
  | one hUpper =>
      exact
        Higham13BlockLUBudgetChain.one (hr := hr)
          (C_L := (n : ℝ) *
            (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
              (maxEntryNormRect hN hN Aglob *
                maxEntryNormRect hN hN AinvGlob))
          (C_U := growthFactorEntry hN Aglob Gglob hApos *
            maxEntryNormRect hN hN Aglob)
          hId hUpper
  | @succ m Ablk pivotInv hA11 hSchur hFull hpivot hsn hA_le_G
      hSchur_le_G hAinv_entry hFirstRow hTail ih =>
      let hs : 0 < (m + 1) * r := Nat.mul_pos (Nat.succ_pos m) hr
      have hL21 :
          maxEntryNormRect hs hr
              ((blockMatrixFirstSplitA21 Ablk *
                ⅟(blockMatrixFirstSplitA11 Ablk) :
                Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤
            (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
              (maxEntryNormRect hN hN Aglob *
                maxEntryNormRect hN hN AinvGlob) := by
        letI : Invertible (blockMatrixFirstSplitA11 Ablk) := hA11
        letI : Invertible (blockMatrixFirstSplitA22 Ablk -
          blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
            blockMatrixFirstSplitA12 Ablk) := hSchur
        letI : Invertible (Matrix.fromBlocks
          (blockMatrixFirstSplitA11 Ablk)
          (blockMatrixFirstSplitA12 Ablk)
          (blockMatrixFirstSplitA21 Ablk)
          (blockMatrixFirstSplitA22 Ablk)) := hFull
        simpa [hs] using
          higham13_problem13_4_L21_eq13_22_premise_from_global_growth_tableau_exact_kappa
            hr hs hN Aglob Gglob AinvGlob
            (blockMatrixFirstSplitA11 Ablk)
            (blockMatrixFirstSplitA12 Ablk)
            (blockMatrixFirstSplitA21 Ablk)
            (blockMatrixFirstSplitA22 Ablk)
            hApos n hsn hA_le_G hSchur_le_G hAinv_entry
      have hL21_pivot :
          maxEntryNormRect hs hr
              ((blockMatrixFirstSplitA21 Ablk * pivotInv 0 :
                Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤
            (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
              (maxEntryNormRect hN hN Aglob *
                maxEntryNormRect hN hN AinvGlob) := by
        simpa [hpivot] using hL21
      exact
        Higham13BlockLUBudgetChain.succ (hr := hr)
          (C_L := (n : ℝ) *
            (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
              (maxEntryNormRect hN hN Aglob *
                maxEntryNormRect hN hN AinvGlob))
          (C_U := growthFactorEntry hN Aglob Gglob hApos *
            maxEntryNormRect hN hN Aglob)
          hpivot hId hL21_pivot hFirstRow ih

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    fixed-ambient global-tableau source chain with the scalar lower-budget
    nonvacuity discharged from an exact ambient right inverse. -/
theorem Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_right_inverse
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
          (maxEntryNormRect hN hN Aglob *
            maxEntryNormRect hN hN AinvGlob))
        (growthFactorEntry hN Aglob Gglob hApos *
          maxEntryNormRect hN hN Aglob)
        m Ablk pivotInv := by
  intro m Ablk pivotInv hcert
  have hId :
      1 ≤ (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
        (maxEntryNormRect hN hN Aglob *
          maxEntryNormRect hN hN AinvGlob) :=
    higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth
      hN Aglob Gglob AinvGlob hApos hRight n hNn hA_le_G
  exact
    Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain
      (r := r) (N := N) (n := n) hr hN Aglob Gglob AinvGlob
      hApos hId hcert

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    recursive Eq.13.22 product witness from the fixed ambient
    global-growth-tableau source chain. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 3 *
                (maxEntryNormRect hN hN Aglob *
                  maxEntryNormRect hN hN AinvGlob) *
                maxEntryNormRect hN hN Aglob := by
  intro m Ablk pivotInv hcert
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
          (maxEntryNormRect hN hN Aglob *
            maxEntryNormRect hN hN AinvGlob))
        (growthFactorEntry hN Aglob Gglob hApos *
          maxEntryNormRect hN hN Aglob)
        m Ablk pivotInv :=
    Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob Gglob AinvGlob
      hApos hRight hNn hA_le_G hcert
  exact
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr hN Aglob Gglob AinvGlob hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    recursive point-row product witness from the fixed ambient global-growth
    tableau source chain plus the still-separate source theorem `rho <= 2`. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob AinvGlob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob)
    (hRho_le_two : growthFactorEntry hN Aglob Gglob hApos ≤ 2) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob AinvGlob
        hApos n m Ablk pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN Aglob *
                  maxEntryNormRect hN hN AinvGlob) *
                maxEntryNormRect hN hN Aglob := by
  intro m Ablk pivotInv hcert
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
          (maxEntryNormRect hN hN Aglob *
            maxEntryNormRect hN hN AinvGlob))
        (growthFactorEntry hN Aglob Gglob hApos *
          maxEntryNormRect hN hN Aglob)
        m Ablk pivotInv :=
    Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob Gglob AinvGlob
      hApos hRight hNn hA_le_G hcert
  exact
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr hN Aglob Gglob AinvGlob hApos n hchain
      hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero fixed-ambient global-tableau source certificate
    instantiates the ambient exact-`κ` budget chain with the canonical
    `nonsingInv` inverse.

    This is the determinant-input companion to
    `Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_right_inverse`;
    it removes the raw ambient right-inverse proof artifact when the ambient
    inverse stored in the source chain is the canonical nonsingular inverse. -/
theorem Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_det_ne_zero
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hdet : Matrix.det (Aglob : Matrix (Fin N) (Fin N) ℝ) ≠ 0)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob
        (nonsingInv N Aglob) hApos n m Ablk pivotInv →
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 2 *
          (maxEntryNormRect hN hN Aglob *
            maxEntryNormRect hN hN (nonsingInv N Aglob)))
        (growthFactorEntry hN Aglob Gglob hApos *
          maxEntryNormRect hN hN Aglob)
        m Ablk pivotInv := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322GlobalTableauSourceChain.to_blockLUBudgetChain_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob Gglob
      (nonsingInv N Aglob) hApos
      ((isInverse_nonsingInv_of_det_ne_zero N Aglob hdet).2)
      hNn hA_le_G hcert

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    determinant-nonzero recursive Eq.13.22 product witness from the
    fixed-ambient global-tableau source chain with the canonical ambient
    `nonsingInv` inverse. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_det_ne_zero
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hdet : Matrix.det (Aglob : Matrix (Fin N) (Fin N) ℝ) ≠ 0)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob
        (nonsingInv N Aglob) hApos n m Ablk pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              (n : ℝ) * (growthFactorEntry hN Aglob Gglob hApos) ^ 3 *
                (maxEntryNormRect hN hN Aglob *
                  maxEntryNormRect hN hN (nonsingInv N Aglob)) *
                maxEntryNormRect hN hN Aglob := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob Gglob
      (nonsingInv N Aglob) hApos
      ((isInverse_nonsingInv_of_det_ne_zero N Aglob hdet).2)
      hNn hA_le_G hcert

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    determinant-nonzero recursive point-row product witness from the
    fixed-ambient global-tableau source chain with the canonical ambient
    `nonsingInv` inverse.  The source-side `rho <= 2` theorem remains an
    explicit Eq.13.23 obligation. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_det_ne_zero
    {r N n : ℕ} (hr : 0 < r) (hN : 0 < N)
    (Aglob Gglob : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hdet : Matrix.det (Aglob : Matrix (Fin N) (Fin N) ℝ) ≠ 0)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hA_le_G : maxEntryNorm hN Aglob ≤ maxEntryNorm hN Gglob)
    (hRho_le_two : growthFactorEntry hN Aglob Gglob hApos ≤ 2) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob Gglob
        (nonsingInv N Aglob) hApos n m Ablk pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN Aglob *
                  maxEntryNormRect hN hN (nonsingInv N Aglob)) *
                maxEntryNormRect hN hN Aglob := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob Gglob
      (nonsingInv N Aglob) hApos
      ((isInverse_nonsingInv_of_det_ne_zero N Aglob hdet).2)
      hNn hA_le_G hRho_le_two hcert

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    fixed-ambient global-tableau Eq.13.23 product witness with `rho <= 2`
    supplied by the mixed matrix-`∞`/max-entry BDD endpoint.

    This wrapper removes the raw global growth-factor side condition from the
    concrete `BlockLUFactSpec` witness surface while keeping the source-chain
    certificate, all-prefix BDD data, and active pivot right-inverse table
    explicit. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_mixed_column_mass
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      AinvGlob hApos n m Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < M,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol M
      (fun i j : Fin M => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  have hRho_le_two :
      growthFactorEntry hFlat (blockMatrixFlatFin A) G hApos ≤ 2 := by
    have hEndpoint :=
      higham13_algorithm13_3_upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_all_leadingBlockPrefixes_blockDiagDomCol_infNorm_diagBound_nonpos_of_pivot_right_inverse
        hM hr A pivotInv invDiagBound hPrefix hDomInf hBound hPivotRight
    simpa [hFlat, G] using hEndpoint.2
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := M * r) (n := n) hr hFlat (blockMatrixFlatFin A)
      G AinvGlob hApos hRight hNn hA_le_G hRho_le_two
      (by simpa [hFlat, G] using hcert)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero form of
    `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_mixed_column_mass`.

    The ambient inverse is the canonical `nonsingInv`; the mixed BDD endpoint
    still supplies the Eq.13.23 growth-factor side condition internally. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_det_ne_zero_of_mixed_column_mass
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
      Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < M,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (fun i j a b => A i j a b) p hp))
    (hDomInf : IsBlockDiagDomCol M
      (fun i j : Fin M => infNorm (A i j)) invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < M,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_mixed_column_mass
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      Ablk chainPivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hcert invDiagBound hPrefix hDomInf hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    full-chain global-tableau Eq.13.23 product witness with `rho <= 2`
    supplied by the mixed matrix-`∞`/max-entry BDD endpoint.

    This is the final-pivot form of the fixed-ambient mixed witness above for
    the common full-chain case.  The all-active pivot right-inverse table and
    ambient determinant/right-inverse proof artifacts are derived internally
    from the source chain, all-prefix nonsingularity table, and terminal
    pivot right-inverse certificate. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin Ablk))
      (_hcert : Higham13Eq1322GlobalTableauSourceChain hr
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
          pivotInv)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
        hApos n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (hNn : ((((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))) →
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
  intro m Ablk pivotInv hApos hcert
  dsimp only
  intro hNn invDiagBound hPrefix hDomInf hBound hFinal
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    blockMatrixFlatFin Ablk
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
      (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix
  have hPivotRight : ∀ k : ℕ, ∀ hk : k < m + 1,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock
          Ablk pivotInv k ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k) :=
    Higham13Eq1322GlobalTableauSourceChain.pivot_right_inverse_of_final
      hcert hFinal
  simpa [hm, hN, A0, Ainv] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_det_ne_zero_of_mixed_column_mass
      (M := m + 1) (r := r) (m := m) (n := n) hr hm
      Ablk pivotInv Ablk pivotInv hApos hdet hNn
      (by simpa [hm, hN, A0] using hcert)
      invDiagBound hPrefix hDomInf hBound hPivotRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    canonical-terminal-pivot form of
    `Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass`.

    The terminal pivot is supplied as the canonical `nonsingInv`; the source
    chain and BDD table supply the remaining pivot and growth-factor data. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hApos : 0 < maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin Ablk))
      (_hcert : Higham13Eq1322GlobalTableauSourceChain hr
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
          pivotInv)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin Ablk))
        hApos n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (hNn : ((((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))) →
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
  intro m Ablk pivotInv hApos hcert
  dsimp only
  intro hNn invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq
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
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) hr hApos hcert hNn invDiagBound hPrefix hDomInf
      hBound hFinalRight

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    fixed-ambient global-tableau source-chain witness with `rho <= 2`
    discharged by the full-flat product-bound/diagonal-update BDD route.

    This is the source-chain-level version of the product-update wrappers
    below: once a fixed-ambient global-tableau certificate has been built for
    any recorded tail, the concrete Algorithm 13.3 product/update hypotheses
    prove the growth-factor side condition needed for the Eq.13.23 product
    bound. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      AinvGlob hApos n m Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  have hRho_le_two :
      growthFactorEntry hFlat (blockMatrixFlatFin A) G hApos ≤ 2 := by
    simpa [hFlat, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hM hr A pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := M * r) (n := n) hr hFlat (blockMatrixFlatFin A)
      G AinvGlob hApos hRight hNn hA_le_G hRho_le_two
      (by simpa [hFlat, G] using hcert)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    reciprocal-table form of the fixed-ambient global-tableau source-chain
    product-update witness. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      AinvGlob hApos n m Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update
      hr hM AinvGlob A pivotInv Ablk chainPivotInv hApos hRight hNn
      hcert invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero form of the fixed-ambient global-tableau source-chain
    product-update witness, using the canonical `nonsingInv` ambient inverse. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
      Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      Ablk chainPivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hcert invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero reciprocal-table form of the fixed-ambient
    global-tableau source-chain product-update witness. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
      Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      Ablk chainPivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hcert invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    matrix-`∞` BDD form of the fixed-ambient global-tableau source-chain
    product/update witness with an explicit ambient right inverse.

    The source BDD hypothesis is stated using matrix `∞` block norms.  This
    wrapper derives the max-entry BDD premise consumed by the existing
    product/update route and derives the diagonal max-entry lower certificate
    from the nonpositive source bounds; the global-tableau source certificate
    and product/update data remain explicit obligations. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_infNorm
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      AinvGlob hApos n m Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDomInf : IsBlockDiagDomCol M (fun i j : Fin M => infNorm (A i j))
      invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update
      hr hM AinvGlob A pivotInv Ablk chainPivotInv hApos hRight hNn
      hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr A invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (A j j)))
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    reciprocal-table/matrix-`∞` BDD form of the fixed-ambient global-tableau
    source-chain product/update witness with an explicit ambient right inverse.
    The reciprocal table supplies the scalar pivot-product premise used by the
    existing route. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal_infNorm
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      AinvGlob hApos n m Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDomInf : IsBlockDiagDomCol M (fun i j : Fin M => infNorm (A i j))
      invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal
      hr hM AinvGlob A pivotInv Ablk chainPivotInv hApos hRight hNn
      hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr A invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (A j j)))
      hInitInv hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero matrix-`∞` BDD form of the fixed-ambient
    global-tableau source-chain product/update witness. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_infNorm_of_det_ne_zero
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
      Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDomInf : IsBlockDiagDomCol M (fun i j : Fin M => infNorm (A i j))
      invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_infNorm
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      Ablk chainPivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hcert invDiagBound stageInvDiagBound hDomInf hBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero reciprocal-table/matrix-`∞` BDD form of the
    fixed-ambient global-tableau source-chain product/update witness. -/
theorem
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_infNorm_of_det_ne_zero
    {M r m n : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (chainPivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hcert : Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
      (blockMatrixFlatFin A)
      (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
        (Nat.mul_pos hM hr) hM hr A pivotInv)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
      Ablk chainPivotInv)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDomInf : IsBlockDiagDomCol M (fun i j : Fin M => infNorm (A i j))
      invDiagBound)
    (hBound : ∀ j : Fin M, invDiagBound j ≤ 0)
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec (m + 1) r Ablk L U ∧
        blockMaxNorm (Nat.succ_pos m) hr L *
            blockMaxNorm (Nat.succ_pos m) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse_of_product_bound_diag_update_reciprocal_infNorm
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      Ablk chainPivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hcert invDiagBound stageInvDiagBound hDomInf hBound hInitInv
      hReciprocal hProduct hDiagUpdate

end NumStability
