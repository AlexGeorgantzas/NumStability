/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# The DGTTRF/DGTTRS source domain is necessarily tridiagonal

The literal DGTTRF initialisation reads only the diagonal and the two adjacent
diagonals of its matrix argument.  Consequently no source-residual estimate
against the *full* input matrix can follow from no-breakdown and a gamma guard
alone.  This file records the smallest symmetric exact-arithmetic witness.

This is a domain discrepancy, not a counterexample to Higham's Aasen theorem:
the actual computed Aasen middle factor is symmetric tridiagonal.  The witness
prevents a future closure theorem from silently omitting that source condition.
-/
import NumStability.Algorithms.Cholesky.AasenAdjacentPivotOperationalMiddleCh11

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentOperational

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenAdjacentGEPP
open NumStability.Ch11Closure.SparseFactor
open NumStability.Ch11Closure.SparseSolve

set_option maxRecDepth 20000

/-- Exact arithmetic for the source-domain discrepancy. -/
noncomputable def residualDomainCounterFP : FPModel :=
  FPModel.exactWithUnitRoundoff 0 (by norm_num)

/-- The symmetric matrix `I + e₀e₂ᵀ + e₂e₀ᵀ`.  Its stored three
diagonals are exactly those of the identity, but it is not tridiagonal. -/
noncomputable def residualDomainCounterT : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => 1

/-- The right-hand side exposes the ignored `(0,2)` entry. -/
noncomputable def residualDomainCounterZ : Fin 3 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

theorem residualDomainCounterT_symm :
    ∀ i j : Fin 3,
      residualDomainCounterT i j = residualDomainCounterT j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem residualDomainCounterT_not_tridiagonal :
    ¬ IsTridiagonal 3 residualDomainCounterT := by
  intro h
  have h02 := h (0 : Fin 3) (2 : Fin 3) (by omega)
  norm_num [residualDomainCounterT] at h02

/-- Since the executor sees the identity, every selected and final pivot is
one. -/
theorem residualDomainCounter_noBreakdown :
    DGTTRFNoBreakdown residualDomainCounterFP residualDomainCounterT := by
  constructor
  · intro k hk
    have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with rfl | rfl <;>
      norm_num [flDGTTRFRun, flDGTTRFStepAt, dgttrfInit,
        residualDomainCounterFP, residualDomainCounterT,
        FPModel.exactWithUnitRoundoff, skipZeroSubFP, finReplace]
  · intro i
    fin_cases i <;>
      norm_num [flDGTTRF, flDGTTRFRun, flDGTTRFStepAt, dgttrfInit,
        residualDomainCounterFP, residualDomainCounterT,
        FPModel.exactWithUnitRoundoff, skipZeroSubFP, finReplace]

theorem residualDomainCounter_gammaValid (k : ℕ) :
    gammaValid residualDomainCounterFP k := by
  simp [gammaValid, residualDomainCounterFP, FPModel.exactWithUnitRoundoff]

/-- The literal solve returns `e₂`, because the stored factor is the identity. -/
theorem residualDomainCounter_solution :
    flDGTTRS residualDomainCounterFP 3 residualDomainCounterT
        residualDomainCounterZ = residualDomainCounterZ := by
  let s := flDGTTRF residualDomainCounterFP 3 residualDomainCounterT
  let q := flDGTTRSForward residualDomainCounterFP s residualDomainCounterZ
  have hdiag : ∀ i : Fin 3, s.d i ≠ 0 := by
    simpa [s] using residualDomainCounter_noBreakdown.2
  have hq : q = residualDomainCounterZ := by
    funext i
    fin_cases i <;>
      norm_num [q, s, flDGTTRSForward, flDGTTRSForwardRun,
        flDGTTRSForwardStepAt, flDGTTRF, flDGTTRFRun,
        flDGTTRFStepAt, dgttrfInit, residualDomainCounterFP,
        residualDomainCounterT, residualDomainCounterZ,
        FPModel.exactWithUnitRoundoff, skipZeroSubFP, finReplace]
  have hU : ∀ i j : Fin 3,
      dgttrfU s i j = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [s, dgttrfU, flDGTTRF, flDGTTRFRun,
        flDGTTRFStepAt, dgttrfInit, residualDomainCounterFP,
        residualDomainCounterT, FPModel.exactWithUnitRoundoff,
        skipZeroSubFP, finReplace]
  obtain ⟨ΔU, hΔU, heq⟩ := flDGTTRSBackward_backward_error
    residualDomainCounterFP s q hdiag (residualDomainCounter_gammaValid 3)
  have hΔU0 : ∀ i j : Fin 3, ΔU i j = 0 := by
    intro i j
    have h := hΔU i j
    norm_num [gamma, residualDomainCounterFP,
      FPModel.exactWithUnitRoundoff] at h
    exact h
  change flDGTTRSBackward residualDomainCounterFP s q =
    residualDomainCounterZ
  rw [hq]
  funext i
  have hi := heq i
  rw [hq] at hi
  simp_rw [hU, hΔU0] at hi
  simpa using hi

/-- The ignored off-band coefficient leaves source residual `-1` in row zero. -/
theorem residualDomainCounter_sourceResidual_zero :
    dgttrsSourceResidual residualDomainCounterT residualDomainCounterZ
      (flDGTTRS residualDomainCounterFP 3 residualDomainCounterT
        residualDomainCounterZ) 0 = -1 := by
  rw [residualDomainCounter_solution]
  norm_num [dgttrsSourceResidual, residualDomainCounterT,
    residualDomainCounterZ, Fin.sum_univ_three]

/-- No uniform theorem of the requested form is possible for arbitrary full
matrix inputs.  The conclusion fails for every proposed operation count `k`:
the model is exact, hence `gamma_k = 0`, while the ignored off-band entry gives
unit residual. -/
theorem higham11_8_arbitrary_matrix_source_residual_not_derivable :
    ¬ (∀ (fp : FPModel) (n : ℕ) (T : Fin n → Fin n → ℝ)
        (z : Fin n → ℝ),
      DGTTRFNoBreakdown fp T →
      ∀ k : ℕ, gammaValid fp k →
      ∀ i : Fin n,
        |dgttrsSourceResidual T z (flDGTTRS fp n T z) i| ≤
          gamma fp k * infNorm T *
            infNormVec (flDGTTRS fp n T z)) := by
  intro h
  have hbad := h residualDomainCounterFP 3 residualDomainCounterT
    residualDomainCounterZ residualDomainCounter_noBreakdown 49
    (residualDomainCounter_gammaValid 49) (0 : Fin 3)
  rw [residualDomainCounter_sourceResidual_zero] at hbad
  norm_num [gamma, residualDomainCounterFP,
    FPModel.exactWithUnitRoundoff] at hbad

end NumStability.Ch11Closure.AasenAdjacentOperational
