/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham (2nd ed.) equation (11.15): original-coordinate corrected endpoint

For `P A Pᵀ = L T Lᵀ`, the final coordinate return is `x = Pᵀ w`, not
the printed `x = P w`.  This file transports the unconditional actual
`DGTTRF`/`DGTTRS` correction through a genuine permutation and gives the
nearby system in the original coordinates.  It deliberately does not use the
conditional printed-radius wrapper.
-/
import NumStability.Algorithms.Cholesky.AasenAdjacentPivotSourceResidualCh11Closure
import NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentOperational

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenDirect
open NumStability.Ch11Closure.AasenDirectGEPP
open NumStability.Ch11Closure.AasenAdjacentGEPP

/-- Matrix of a row permutation `sigma`: row `i` selects source row
`sigma i`. -/
def aasenPermutationMatrix {n : ℕ} (sigma : Fin n → Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => if j = sigma i then 1 else 0

/-- Return a vector from permuted coordinates to the source coordinates. -/
noncomputable def aasenUnpermuteVector {n : ℕ} (sigma : Fin n → Fin n)
    (hsigma : IsPermutation n sigma) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w ((Equiv.ofBijective sigma hsigma).symm i)

/-- Transport a perturbation by the same row and column permutation. -/
noncomputable def aasenUnpermuteMatrix {n : ℕ} (sigma : Fin n → Fin n)
    (hsigma : IsPermutation n sigma) (E : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => E ((Equiv.ofBijective sigma hsigma).symm i)
    ((Equiv.ofBijective sigma hsigma).symm j)

theorem aasenPermutationMatrix_mulVec (n : ℕ) (sigma : Fin n → Fin n)
    (b : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, aasenPermutationMatrix sigma i j * b j = b (sigma i) := by
  simp [aasenPermutationMatrix]

theorem aasenUnpermuteVector_eq_transpose_mulVec {n : ℕ}
    (sigma : Fin n → Fin n) (hsigma : IsPermutation n sigma)
    (w : Fin n → ℝ) (i : Fin n) :
    aasenUnpermuteVector sigma hsigma w i =
      ∑ j : Fin n, aasenPermutationMatrix sigma j i * w j := by
  classical
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective sigma hsigma
  have hsum := Equiv.sum_comp e.symm
    (fun k : Fin n => aasenPermutationMatrix sigma k i * w k)
  rw [← hsum]
  have hsigma_inv : ∀ k : Fin n,
      sigma ((Equiv.ofBijective sigma hsigma).symm k) = k := by
    intro k
    change e (e.symm k) = k
    exact e.apply_symm_apply k
  simp [e, aasenPermutationMatrix, aasenUnpermuteVector, hsigma_inv]

theorem aasenUnpermuteMatrix_infNorm {n : ℕ}
    (sigma : Fin n → Fin n) (hsigma : IsPermutation n sigma)
    (E : Fin n → Fin n → ℝ) :
    infNorm (aasenUnpermuteMatrix sigma hsigma E) = infNorm E := by
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective sigma hsigma
  have hperm :
      higham9_2_rowColPermutedMatrix
          (aasenUnpermuteMatrix sigma hsigma E) sigma sigma = E := by
    funext i j
    change E (e.symm (e i)) (e.symm (e j)) = E i j
    simp
  have hnorm := higham9_2_rowColPermutedMatrix_infNorm
    (aasenUnpermuteMatrix sigma hsigma E) hsigma hsigma
  rw [hperm] at hnorm
  exact hnorm.symm

/-- **Corrected original-coordinate Aasen solve endpoint (Theorem 11.8 /
equation (11.15)).**

Run the literal rounded Aasen factorization on the pre-permuted symmetric
matrix `Aperm i j = A (sigma i) (sigma j)`, use the actual adjacent-pivot
`DGTTRF`/`DGTTRS` middle solve, and return `x = Pᵀ w`.  Under only genuine
permutation, nonbreakdown, and floating-point validity hypotheses there is an
explicitly budgeted perturbation of the *original* matrix making `x` exact.
The middle budget retains its exact optimal-backward-error interpretation.
-/
theorem higham11_8_aasen_backward_error_actual_dgttrs_original_corrected
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (sigma : Fin n → Fin n) (hsigma : IsPermutation n sigma)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n
      (higham9_2_rowColPermutedMatrix A sigma sigma))
    (hnb : DGTTRFNoBreakdown fp
      (flAasen fp n
        (higham9_2_rowColPermutedMatrix A sigma sigma)).That)
    (hval : gammaValid fp (3 * n)) :
    let Aperm := higham9_2_rowColPermutedMatrix A sigma sigma
    let Pmat := aasenPermutationMatrix sigma
    let Lh := (flAasen fp n Aperm).Lhat
    let Th := (flAasen fp n Aperm).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let y := flDGTTRS fp n Th z
    let DeltaT := dgttrsSparseResidualCorrection hn Th z y
    let BT := dgttrsSparseResidualBudget hn Th z y
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let x := aasenUnpermuteVector sigma hsigma w
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        |DeltaA i j| ≤
          Bfactor ((Equiv.ofBijective sigma hsigma).symm i)
              ((Equiv.ofBijective sigma hsigma).symm j) +
            Bsolve ((Equiv.ofBijective sigma hsigma).symm i)
              ((Equiv.ofBijective sigma hsigma).symm j)) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * x j = b i) ∧
      infNorm DeltaA ≤ infNorm Bfactor + infNorm Bsolve ∧
      infNorm BT = dgttrsOptimalBackwardError Th z y ∧
      ∀ E : Fin n → Fin n → ℝ,
        (∀ i : Fin n, ∑ j : Fin n, (Th i j + E i j) * y j = z i) →
        infNorm DeltaT ≤ infNorm E := by
  dsimp only
  let Aperm := higham9_2_rowColPermutedMatrix A sigma sigma
  let Pmat := aasenPermutationMatrix sigma
  let Lh := (flAasen fp n Aperm).Lhat
  let Th := (flAasen fp n Aperm).That
  let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
  let z := fl_forwardSub fp n Lh rhs
  let y := flDGTTRS fp n Th z
  let DeltaT := dgttrsSparseResidualCorrection hn Th z y
  let BT := dgttrsSparseResidualBudget hn Th z y
  let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
  let w := fl_backSub fp n Uouter y
  let x := aasenUnpermuteVector sigma hsigma w
  let Bfactor : Fin n → Fin n → ℝ := fun i j =>
    gamma fp (3 * n) *
      ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
  let Bsolve : Fin n → Fin n → ℝ :=
    higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
  have hsymmPerm : ∀ i j : Fin n, Aperm i j = Aperm j i := by
    intro i j
    exact hsymm _ _
  obtain ⟨DeltaPA, hDeltaPA, hsourcePA, hnormPA, hoptimal, hminimal⟩ :=
    higham11_8_aasen_backward_error_direct_actual_dgttrs_corrected
      fp n hn Aperm Pmat b hsymmPerm hp hnb hval
  let DeltaA := aasenUnpermuteMatrix sigma hsigma DeltaPA
  refine ⟨DeltaA, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hDeltaPA _ _
  · intro i
    classical
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective sigma hsigma
    have hrow := hsourcePA (e.symm i)
    change (∑ j : Fin n,
      (Aperm (e.symm i) j + DeltaPA (e.symm i) j) * w j) =
        rhs (e.symm i) at hrow
    have hrhs : rhs (e.symm i) = b i := by
      rw [show rhs (e.symm i) = b (sigma (e.symm i)) by
        simpa [rhs, Pmat] using
          aasenPermutationMatrix_mulVec n sigma b (e.symm i)]
      change b (e (e.symm i)) = b i
      simp
    rw [hrhs] at hrow
    have hsigma_inv_i : sigma (e.symm i) = i := by
      change e (e.symm i) = i
      exact e.apply_symm_apply i
    have hrow' :
        (∑ j : Fin n,
          (A i (sigma j) + DeltaPA (e.symm i) j) * w j) = b i := by
      simpa [Aperm, higham9_2_rowColPermutedMatrix,
        higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
        hsigma_inv_i] using hrow
    have hsum := Equiv.sum_comp e
      (fun j : Fin n => (A i j + DeltaA i j) * x j)
    rw [← hsum]
    simpa [Aperm, higham9_2_rowColPermutedMatrix,
      higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
      DeltaA, aasenUnpermuteMatrix, x, aasenUnpermuteVector, e] using hrow'
  · calc
      infNorm DeltaA = infNorm DeltaPA := by
        simpa [DeltaA] using
          aasenUnpermuteMatrix_infNorm sigma hsigma DeltaPA
      _ ≤ infNorm Bfactor + infNorm Bsolve := hnormPA
  · exact hoptimal
  · exact hminimal

end NumStability.Ch11Closure.AasenAdjacentOperational
